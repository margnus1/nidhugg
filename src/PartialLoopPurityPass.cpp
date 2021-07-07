/* Copyright (C) 2021 Magnus Lång
 *
 * This file is part of Nidhugg.
 *
 * Nidhugg is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Nidhugg is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

#include <config.h>

#include "CheckModule.h"
#include "PartialLoopPurityPass.h"
#include "SpinAssumePass.h"

#include <llvm/Pass.h>
#include <llvm/Analysis/LoopPass.h>
#if defined(HAVE_LLVM_IR_DOMINATORS_H)
#include <llvm/IR/Dominators.h>
#elif defined(HAVE_LLVM_ANALYSIS_DOMINATORS_H)
#include <llvm/Analysis/Dominators.h>
#endif
#if defined(HAVE_LLVM_IR_FUNCTION_H)
#include <llvm/IR/Function.h>
#elif defined(HAVE_LLVM_FUNCTION_H)
#include <llvm/Function.h>
#endif
#if defined(HAVE_LLVM_IR_INSTRUCTIONS_H)
#include <llvm/IR/Instructions.h>
#elif defined(HAVE_LLVM_INSTRUCTIONS_H)
#include <llvm/Instructions.h>
#endif
#if defined(HAVE_LLVM_IR_LLVMCONTEXT_H)
#include <llvm/IR/LLVMContext.h>
#elif defined(HAVE_LLVM_LLVMCONTEXT_H)
#include <llvm/LLVMContext.h>
#endif
#if defined(HAVE_LLVM_IR_MODULE_H)
#include <llvm/IR/Module.h>
#elif defined(HAVE_LLVM_MODULE_H)
#include <llvm/Module.h>
#endif
#if defined(HAVE_LLVM_SUPPORT_CALLSITE_H)
#include <llvm/Support/CallSite.h>
#elif defined(HAVE_LLVM_IR_CALLSITE_H)
#include <llvm/IR/CallSite.h>
#endif
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/Debug.h>

#include <unordered_map>
#include <sstream>

#ifdef LLVM_HAS_TERMINATORINST
typedef llvm::TerminatorInst TerminatorInst;
#else
typedef llvm::Instruction TerminatorInst;
#endif

namespace {
  /* Not reentrant */
  static const llvm::DominatorTree *DominatorTree;

  struct PurityCondition {
    struct BinaryPredicate {
      llvm::Value *lhs = nullptr, *rhs = nullptr;
      /* FCMP_TRUE and FCMP_FALSE are used as special values indicating
       * unconditional purity
       */
      llvm::CmpInst::Predicate op = llvm::CmpInst::FCMP_TRUE;

      BinaryPredicate() {}
      BinaryPredicate(bool static_value) {
        op = static_value ? llvm::CmpInst::FCMP_TRUE : llvm::CmpInst::FCMP_FALSE;
      }
      BinaryPredicate(llvm::CmpInst::Predicate op, llvm::Value *lhs,
                      llvm::Value *rhs)
        : lhs(lhs), rhs(rhs), op(op) {
        assert(!(is_true() || is_false()) || (lhs == nullptr && rhs == nullptr));
      }

      bool is_true() const {
        assert(!(op == llvm::CmpInst::FCMP_TRUE && (lhs || rhs)));
        return op == llvm::CmpInst::FCMP_TRUE;
      }
      bool is_false() const {
        assert(!(op == llvm::CmpInst::FCMP_FALSE && (lhs || rhs)));
        return op == llvm::CmpInst::FCMP_FALSE;
      }

      BinaryPredicate negate() const {
        return {llvm::CmpInst::getInversePredicate(op), lhs, rhs};
      }

      // IDEA: Use operator| for join (and operator& for meet, if needed),
      // unless it's confusing
      BinaryPredicate operator&(const BinaryPredicate &other) const {
        if (other.is_true() || *this == other) return *this;
        if (is_true()) return other;
        return false;
      }
      BinaryPredicate &operator&=(const BinaryPredicate &other) {
        // if (other.is_true() || *this == other) return *this;
        // if (is_true()) return *this = other;
        // op = llvm::CmpInst::FCMP_FALSE;
        // lhs = rhs = nullptr;
        // return *this;
        return *this = (*this & other);
      }

      bool operator!=(const BinaryPredicate &other) const { return !(*this == other); }
      bool operator==(const BinaryPredicate &other) const {
        assert(!(is_true() || is_false()) || (lhs == nullptr && rhs == nullptr));
        return lhs == other.lhs && rhs == other.rhs && op == other.op;
      }
      bool operator<(const BinaryPredicate &other) const {
        if (other.is_true() && !is_true()) return true;
        if (is_false() && !other.is_false()) return true;
        return false;
      }
      bool operator<=(const BinaryPredicate &other) const {
        return *this == other || *this < other;
      }
    } pred;

    /* Earliest location that can support an insertion. nullptr means
     * that any location is fine. */
    llvm::Instruction *insertion_point = nullptr;

    PurityCondition() {}
    PurityCondition(bool static_pred, llvm::Instruction *insertion_point = nullptr)
      : pred(static_pred), insertion_point(static_pred ? insertion_point : nullptr) {}
    PurityCondition(llvm::CmpInst::Predicate op, llvm::Value *lhs,
                    llvm::Value *rhs) : pred(op, lhs, rhs) {}
    // PurityCondition(BinaryPredicate pred, llvm::Instruction *insertion_point)
    //   : pred(std::move(pred)), insertion_point(insertion_point) {}

    bool is_true() const { return pred.is_true() && !insertion_point; }
    bool is_false() const {
      assert(!(pred.is_false() && insertion_point));
      return pred.is_false();
    }
    PurityCondition negate() const {
      PurityCondition res = *this;
      res.pred = pred.negate();
      return res;
    }

    // IDEA: Use operator| for join (and operator& for meet, if needed),
    // unless it's confusing
    PurityCondition operator&(const PurityCondition &other) const {
      PurityCondition res;
      if (!insertion_point) res.insertion_point = other.insertion_point;
      else if (!other.insertion_point) res.insertion_point = insertion_point;
      else if (insertion_point == other.insertion_point) res.insertion_point = insertion_point;
      else if (DominatorTree->dominates(insertion_point, other.insertion_point)) {
        res.insertion_point = other.insertion_point;
      } else if (DominatorTree->dominates(other.insertion_point, insertion_point)) {
        res.insertion_point = insertion_point;
      } else {
        /* TODO: We have to find the least common denominator */
        llvm::dbgs() << "Meeting insertion points general case not implemented\n";
        return false; // Underapproximating for now
      }

      res.pred = pred & other.pred;
      if (res.pred.is_false()) res.insertion_point = nullptr; // consistency
      return res;
    }
    PurityCondition &operator&=(const PurityCondition &other) {
      return *this = (*this & other);
    }

  private:
    llvm::Instruction *join_insertion_points(llvm::Instruction *other) const {
      llvm::Instruction *me = this->insertion_point;
      if (!me || !other) return nullptr;
      if (DominatorTree->dominates(other, me)) {
        assert(other != me);
        return other;
      }
      return me;
    }
  public:
    PurityCondition operator|(const PurityCondition &other) const {
      if (other.is_false()) return *this;
      if (is_false()) return other;
      if (pred.lhs == other.pred.lhs && pred.rhs == other.pred.rhs) {
        /* Maybe this can be made more precise. F.ex. <= | >= is also
         * true. There might be such a check in LLVM already. */
        if (llvm::CmpInst::getInversePredicate(pred.op) == other.pred.op) {
          return PurityCondition(true, join_insertion_points(other.insertion_point));
        } else if (pred == other.pred) {
          PurityCondition res = *this;
          res.insertion_point = join_insertion_points(other.insertion_point);
          return res;
        }
      }
      /* XXX: We have to underapproximate :( */
      if (*this < other) return other;
      else return *this;
    }

    bool operator!=(const PurityCondition &other) { return !(*this == other); }
    bool operator==(const PurityCondition &other) {
      return pred == other.pred && insertion_point == other.insertion_point;
    }
    bool operator<(const PurityCondition &other) const {
      if (is_false()) return !other.is_false();
      else if (!other.insertion_point && insertion_point /* < */) return pred <= other.pred;
      else if (!insertion_point && other.insertion_point /* > */) return false;
      else if (insertion_point == other.insertion_point /* == */) return pred < other.pred;
      else if (insertion_point && other.insertion_point) {
        if (DominatorTree->dominates(other.insertion_point, insertion_point) /* < */) {
          return pred <= other.pred;
        }
        return false; /* Incomparable */
      }

      llvm_unreachable("All cases of insertion_point comparision covered above");
    }

  };
  typedef std::unordered_map<const llvm::BasicBlock*,PurityCondition> PurityConditions;

  const char *getPredicateName(llvm::CmpInst::Predicate pred) {
    using llvm::ICmpInst; using llvm::FCmpInst;
    switch (pred) {
    default:                   return "unknown";
    case FCmpInst::FCMP_FALSE: return "false";
    case FCmpInst::FCMP_OEQ:   return "oeq";
    case FCmpInst::FCMP_OGT:   return "ogt";
    case FCmpInst::FCMP_OGE:   return "oge";
    case FCmpInst::FCMP_OLT:   return "olt";
    case FCmpInst::FCMP_OLE:   return "ole";
    case FCmpInst::FCMP_ONE:   return "one";
    case FCmpInst::FCMP_ORD:   return "ord";
    case FCmpInst::FCMP_UNO:   return "uno";
    case FCmpInst::FCMP_UEQ:   return "ueq";
    case FCmpInst::FCMP_UGT:   return "ugt";
    case FCmpInst::FCMP_UGE:   return "uge";
    case FCmpInst::FCMP_ULT:   return "ult";
    case FCmpInst::FCMP_ULE:   return "ule";
    case FCmpInst::FCMP_UNE:   return "une";
    case FCmpInst::FCMP_TRUE:  return "true";
    case ICmpInst::ICMP_EQ:    return "eq";
    case ICmpInst::ICMP_NE:    return "ne";
    case ICmpInst::ICMP_SGT:   return "sgt";
    case ICmpInst::ICMP_SGE:   return "sge";
    case ICmpInst::ICMP_SLT:   return "slt";
    case ICmpInst::ICMP_SLE:   return "sle";
    case ICmpInst::ICMP_UGT:   return "ugt";
    case ICmpInst::ICMP_UGE:   return "uge";
    case ICmpInst::ICMP_ULT:   return "ult";
    case ICmpInst::ICMP_ULE:   return "ule";
    }
  }

  llvm::Instruction::OtherOps getPredicateOpcode(llvm::CmpInst::Predicate pred) {
    using llvm::ICmpInst; using llvm::FCmpInst;
    switch (pred) {
    case ICmpInst::BAD_ICMP_PREDICATE:
    case FCmpInst::BAD_FCMP_PREDICATE:
    default:
      llvm::dbgs() << "Predicate " << pred << " unknown!\n";
      assert(false && "unknown predicate"); abort();
    case ICmpInst::ICMP_EQ:  case ICmpInst::ICMP_NE:
    case ICmpInst::ICMP_SGT: case ICmpInst::ICMP_SGE:
    case ICmpInst::ICMP_SLT: case ICmpInst::ICMP_SLE:
    case ICmpInst::ICMP_UGT: case ICmpInst::ICMP_UGE:
    case ICmpInst::ICMP_ULT: case ICmpInst::ICMP_ULE:
      return llvm::Instruction::OtherOps::ICmp;
    case FCmpInst::FCMP_FALSE: case FCmpInst::FCMP_TRUE:
      assert(false && "Predicates false & true should not generate cmp insts");
    case FCmpInst::FCMP_OEQ: case FCmpInst::FCMP_OGT:
    case FCmpInst::FCMP_OGE: case FCmpInst::FCMP_OLT:
    case FCmpInst::FCMP_OLE: case FCmpInst::FCMP_ONE:
    case FCmpInst::FCMP_ORD: case FCmpInst::FCMP_UNO:
    case FCmpInst::FCMP_UEQ: case FCmpInst::FCMP_UGT:
    case FCmpInst::FCMP_UGE: case FCmpInst::FCMP_ULT:
    case FCmpInst::FCMP_ULE: case FCmpInst::FCMP_UNE:
      return llvm::Instruction::OtherOps::FCmp;
    }
  }

  enum class Tristate {
    FALSE,
    TRUE,
    MAYBE,
  };

  Tristate predicateSatisfiedOnEquality(llvm::CmpInst::Predicate pred) {
    using llvm::ICmpInst; using llvm::FCmpInst;
    switch (pred) {
    case ICmpInst::ICMP_EQ:
    case ICmpInst::ICMP_SGE: case ICmpInst::ICMP_SLE:
    case ICmpInst::ICMP_UGE: case ICmpInst::ICMP_ULE:
      return Tristate::TRUE;
    case ICmpInst::ICMP_NE:
    case ICmpInst::ICMP_SGT: case ICmpInst::ICMP_SLT:
    case ICmpInst::ICMP_UGT: case ICmpInst::ICMP_ULT:
      return Tristate::FALSE;
    default:
      return Tristate::MAYBE;
    }
  }

  llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const PurityCondition &cond) {
    if (cond.pred.is_true()) os << "true";
    else if (cond.pred.is_false()) os << "false";
    else {
      cond.pred.lhs->printAsOperand(os);
      os << " " << getPredicateName(cond.pred.op) << " ";
      cond.pred.rhs->printAsOperand(os);
    }
    if (cond.insertion_point) {
      os << " after " << *cond.insertion_point;
    }
    return os;
  }

  llvm::Instruction *maybeFindUserLocation
  (llvm::User *U, llvm::SmallPtrSet<llvm::User*, 16> &Set) {
    if (llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(U)) return I;
    if (Set.count(U)) {
      llvm::dbgs() << *U << " is cyclic!\n";
      abort();
    }
    else Set.insert(U);
    llvm::Instruction *Location = nullptr;

    for (llvm::Use &Use : U->uses()) {
      if (llvm::User *U2 = llvm::dyn_cast<llvm::User>(Use.get())) {
        if (U2 == U) continue;
        if (llvm::Instruction *I = maybeFindUserLocation(U2, Set)) {
          assert(!Location);
          Location = I;
        }
      }
    }

    return Location;
  }

  llvm::Instruction *maybeFindUserLocationOrNull(llvm::User *U) {
    if (!U) return nullptr;
    llvm::SmallPtrSet<llvm::User*, 16> Set;
    return maybeFindUserLocation(U, Set);
  }

  llvm::Instruction *maybeFindValueLocation(llvm::Value *V) {
    if (llvm::User *U = llvm::dyn_cast<llvm::User>(V)) {
      llvm::SmallPtrSet<llvm::User*, 16> Set;
      return maybeFindUserLocation(U, Set);
    } else {
      return nullptr;
    }
  }

  void maybeResolvePhi(llvm::Value *&V, const llvm::BasicBlock *From,
                              const llvm::BasicBlock *To) {
    llvm::PHINode *N = llvm::dyn_cast_or_null<llvm::PHINode>(V);
    if (!N || N->getParent() != To) return;
    V = N->getIncomingValueForBlock(From);
  }

  void collapseTautologies(PurityCondition &cond) {
    if (cond.pred.is_true() || cond.pred.is_false()) return;
    if (cond.pred.rhs == cond.pred.lhs) {
      Tristate eq = predicateSatisfiedOnEquality(cond.pred.op);
      if (eq != Tristate::MAYBE) {
        cond.pred = (eq == Tristate::TRUE);
      }
    }

    if (cond.pred.is_false()) cond.insertion_point = nullptr;
  }

  PurityCondition getIn(const llvm::Loop *L, PurityConditions &conds,
                        const llvm::BasicBlock *From,
                        const llvm::BasicBlock *To) {
    if (To == L->getHeader()) {
      /* Check for data leaks along the back edge */
      // llvm::dbgs() << "Checking " << From->getName() << "->" << To->getName()
      //              << " for escaping phis: \n";
      for (const llvm::Instruction *I = &*To->begin();
           I != To->getFirstNonPHI(); I = I->getNextNode()) {
        const llvm::PHINode *Phi = llvm::cast<llvm::PHINode>(I);
        llvm::Value *V = Phi->getIncomingValueForBlock(From);
        // llvm::dbgs() << "  "; Phi->printAsOperand(llvm::dbgs());
        // llvm::dbgs() << ": "; V->printAsOperand(llvm::dbgs()); llvm::dbgs() << "\n";
        if (llvm::Instruction *VI = maybeFindValueLocation(V)) {
          if (L->contains(VI)) {
            // llvm::dbgs() << "  leak: "; V->printAsOperand(llvm::dbgs());
            // llvm::dbgs() << " through "; Phi->printAsOperand(llvm::dbgs());
            // llvm::dbgs() << "\n";
            return false; /* Leak */
          }
        }
      }
      return true;
    }
    if (!L->contains(To)) return false;
    PurityCondition in = conds[To];
    maybeResolvePhi(in.pred.rhs, From, To);
    maybeResolvePhi(in.pred.lhs, From, To);
    collapseTautologies(in);
    return in;
  }

  PurityCondition computeOut(const llvm::Loop *L, PurityConditions &conds,
                             const llvm::BasicBlock *BB) {
    if (auto *branch = llvm::dyn_cast<llvm::BranchInst>(BB->getTerminator())) {
      if (auto *cmp = llvm::dyn_cast_or_null<llvm::CmpInst>
          (branch->isConditional() ? branch->getCondition() : nullptr)) {
        PurityCondition trueIn = getIn(L, conds, BB, branch->getSuccessor(0));
        PurityCondition falseIn = getIn(L, conds, BB, branch->getSuccessor(1));
        if (trueIn == falseIn) return trueIn;
        // If the operands are in the loop, we can check them for
        // purity; if not, the condition should just be false. That way,
        // we won't waste good conditions in the overapproximations
        PurityCondition cmpCond(cmp->getPredicate(), cmp->getOperand(0), cmp->getOperand(1));
        // if (trueIn.is_true()) return falseIn | cmpCond;
        // if (falseIn.is_true()) return trueIn | cmpCond.negate();
        // llvm::dbgs() << "   lhs: " << (falseIn | cmpCond) << "\n";
        // llvm::dbgs() << "    trueIn: " << trueIn << "\n";
        // llvm::dbgs() << "    cmpCond.negate(): " << cmpCond.negate() << "\n";
        // llvm::dbgs() << "   rhs: " << (trueIn | cmpCond.negate()) << "\n";
        // assert(!(trueIn | cmpCond.negate()).is_false() || (trueIn.is_false() && cmpCond.is_false()));
        return (falseIn | cmpCond) & (trueIn | cmpCond.negate());
      }
    }

    /* Generic implementation; no concern for branch conditions */
    PurityCondition cond;
    for (const llvm::BasicBlock *s : llvm::successors(BB)) {
      cond &= getIn(L, conds, BB, s);
    }
    return cond;
  }

  PurityCondition instructionPurity(llvm::Loop *L, llvm::Instruction &I) {
    if (!I.mayReadOrWriteMemory()
        && llvm::isSafeToSpeculativelyExecute(&I)) return true;
    if (llvm::isa<llvm::PHINode>(I)) return true;

    if (const llvm::LoadInst *Ld = llvm::dyn_cast<llvm::LoadInst>(&I)) {
      /* No-segfaulting */
      if ((llvm::isa<llvm::GlobalValue>(Ld->getPointerOperand())
           || llvm::isa<llvm::AllocaInst>(Ld->getPointerOperand()))) {
        return true;
      } else {
        return PurityCondition(true, &I);
      }
    }
    if (!I.mayWriteToMemory()) {
      if (llvm::isSafeToSpeculativelyExecute(&I)) {
        llvm::dbgs() << "Wow, a safe-to-speculate loading inst: " << I << "\n";
        return true;
      } else {
        return PurityCondition(true, &I);
      }
    }
    /* XXX: Do me */

    return false;
  }

  PurityConditions analyseLoop(llvm::Loop *L) {
    PurityConditions conds;
    const auto &blocks = L->getBlocks();
    bool changed;
    // llvm::dbgs() << "Analysing " << *L;
    do {
      changed = false;
      // Assume it's in reverse postorder, or some suitable order
      for (auto it = blocks.rbegin(); it != blocks.rend(); ++it) {
        llvm::BasicBlock *BB = *it;
        PurityCondition cond = computeOut(L, conds, BB);
        // llvm::dbgs() << "  out of " << BB->getName() << ": " << cond << "\n";
        /* Skip the terminator */
        for (auto it = BB->rbegin(); ++it != BB->rend();) {
          cond &= instructionPurity(L, *it);
        }
        if (conds[BB] != cond) {
          // llvm::dbgs() << " " << BB->getName() << ": " << cond << "\n";
          if (!(cond < conds[BB])) {
            llvm::dbgs() << cond << "\n" << conds[BB] << "\n";
            assert(cond < conds[BB]);
            abort();
          }
          changed = true;
          conds[BB] = cond;
        }
      }
    } while(changed);
    return conds;
  }

  bool dominates_or_equals(const llvm::DominatorTree &DT,
                           llvm::Instruction *Def, llvm::Instruction *User) {
    return Def == User || DT.dominates(Def, User);
  }

  llvm::Instruction *findInsertionPoint(llvm::Loop *L,
                                        const llvm::DominatorTree &DT,
                                        const PurityCondition &cond) {
    if (llvm::Instruction *IPT = cond.insertion_point) {
      if (llvm::Instruction *LHS = maybeFindUserLocationOrNull
          (llvm::dyn_cast<llvm::User>(cond.pred.lhs))) {
        if (llvm::Instruction *RHS = maybeFindUserLocationOrNull
            (llvm::dyn_cast<llvm::User>(cond.pred.rhs))) {
          if (dominates_or_equals(DT, LHS, IPT) &&
              dominates_or_equals(DT, RHS, IPT)) return IPT->getNextNode();
          if (dominates_or_equals(DT, IPT, RHS) &&
              dominates_or_equals(DT, LHS, RHS)) return RHS->getNextNode();
          if (dominates_or_equals(DT, IPT, LHS) &&
              dominates_or_equals(DT, RHS, LHS)) return LHS->getNextNode();
          /* uh oh, hard case */
          assert(false && "Implement me"); abort();
        } else {
          if (dominates_or_equals(DT, LHS, IPT)) return IPT->getNextNode();
          if (dominates_or_equals(DT, IPT, LHS)) return LHS->getNextNode();
          /* uh oh, hard case */
          assert(false && "Implement me"); abort();
        }
      } else if (llvm::Instruction *RHS = maybeFindUserLocationOrNull
            (llvm::dyn_cast<llvm::User>(cond.pred.rhs))) {
          if (dominates_or_equals(DT, LHS, IPT)) return IPT->getNextNode();
          if (dominates_or_equals(DT, IPT, LHS)) return LHS->getNextNode();
          /* uh oh, hard case */
          assert(false && "Implement me"); abort();
      } else {
        return IPT->getNextNode();
      }
    } else {
      if (llvm::Instruction *LHS = maybeFindUserLocationOrNull
          (llvm::dyn_cast<llvm::User>(cond.pred.lhs))) {
        if (llvm::Instruction *RHS = maybeFindUserLocationOrNull
            (llvm::dyn_cast<llvm::User>(cond.pred.rhs))) {
          if (dominates_or_equals(DT, LHS, RHS)) return RHS->getNextNode();
          if (dominates_or_equals(DT, RHS, LHS)) return LHS->getNextNode();
          /* uh oh, hard case */
          assert(false && "Implement me"); abort();
        } else {
          return LHS->getNextNode();
        }
      } else if (llvm::Instruction *RHS = maybeFindUserLocationOrNull
                 (llvm::dyn_cast<llvm::User>(cond.pred.rhs))) {
        return RHS->getNextNode();
      } else {
        return &*L->getHeader()->getFirstInsertionPt();
      }
    }
    llvm_unreachable("All cases covered in findInsertionPoint");
  }
}

void PartialLoopPurityPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const{
  AU.addRequired<llvm::LLVM_DOMINATOR_TREE_PASS>();
  AU.addRequired<DeclareAssumePass>();
  AU.addPreserved<DeclareAssumePass>();
}

bool PartialLoopPurityPass::runOnLoop(llvm::Loop *L, llvm::LPPassManager &LPM){
  // llvm::dbgs() << "Analysing " << L->getHeader()->getParent()->getName() << ":\n";
  // llvm::dbgs() << *L->getHeader()->getParent();
  const llvm::DominatorTree &DT
    = getAnalysis<llvm::LLVM_DOMINATOR_TREE_PASS>().getDomTree();
  assert(!DominatorTree);
  DominatorTree = &DT;
  PurityConditions conditions = analyseLoop(L);
  PurityCondition headerCond = conditions[L->getHeader()];
  if (headerCond.is_false()) {
    // llvm::dbgs() << "Loop " << L->getHeader()->getParent()->getName() << ":"
    //              << *L << " isn't pure\n";
    DominatorTree = nullptr;
    return false;
  } else {
    llvm::dbgs() << "Partially pure loop found in "
                 << L->getHeader()->getParent()->getName() << "():\n";
    L->print(llvm::dbgs(), 2);
    llvm::dbgs() << " Purity condition: " << headerCond << "\n";
  }

  if (headerCond.pred.is_true()) {
    /* Insert assume(false); at the beginning of the header */
    llvm::dbgs() << "Full purity not implemented\n";
    return false;
  }
  llvm::Instruction *I = findInsertionPoint(L, DT, headerCond);
  llvm::dbgs() << " Insertion point: " << *I << "\n";
  llvm::CmpInst *CmpI = llvm::ICmpInst::Create
    (getPredicateOpcode(headerCond.pred.op),
     llvm::CmpInst::getInversePredicate(headerCond.pred.op),
     headerCond.pred.lhs, headerCond.pred.rhs, "negated.pp.cond", I);
  llvm::Value *Cond = CmpI;
  llvm::Function *F_assume = L->getHeader()->getParent()->getParent()
    ->getFunction("__VERIFIER_assume");
  {
    llvm::Type *arg_ty = F_assume->arg_begin()->getType();
    assert(arg_ty->isIntegerTy());
    if(arg_ty->getIntegerBitWidth() != 1){
      Cond = new llvm::ZExtInst(Cond, arg_ty,"",I);
    }
  }
  llvm::CallInst::Create(F_assume,{Cond},"",I);

  // llvm::dbgs() << "Rewritten:\n";
  // llvm::dbgs() << *L->getHeader()->getParent();
  assert(!llvm::verifyFunction(*L->getHeader()->getParent(), &llvm::dbgs()));

  DominatorTree = nullptr;
  return true;
}

char PartialLoopPurityPass::ID = 0;
static llvm::RegisterPass<PartialLoopPurityPass> X
("partial-loop-purity",
 "Bound pure and partially pure loops with __VERIFIER_assumes.");
