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

#include "llvm/IR/Verifier.h"
#include "llvm/Support/Debug.h"
#include <config.h>

#include <unordered_map>

#include <llvm/Pass.h>
#include <llvm/Analysis/LoopPass.h>
#include <unordered_map>
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

#include "CheckModule.h"
#include "PartialLoopPurityPass.h"
#include "SpinAssumePass.h"

#ifdef LLVM_HAS_TERMINATORINST
typedef llvm::TerminatorInst TerminatorInst;
#else
typedef llvm::Instruction TerminatorInst;
#endif

namespace {
  static const llvm::DominatorTree *DominatorTree;

  struct PurityCondition {
    llvm::Value *lhs = nullptr, *rhs = nullptr;
    /* FCMP_TRUE and FCMP_FALSE are used as special values indicating
     * unconditional purity
     */
    llvm::CmpInst::Predicate op = llvm::CmpInst::FCMP_TRUE;
    PurityCondition() {}
    PurityCondition(bool static_value) {
      op = static_value ? llvm::CmpInst::FCMP_TRUE : llvm::CmpInst::FCMP_FALSE;
    }
    PurityCondition(llvm::CmpInst::Predicate op, llvm::Value *lhs,
                    llvm::Value *rhs)
      : lhs(lhs), rhs(rhs), op(op) {
      assert(!(is_true() || is_false()) || (lhs == nullptr && rhs == nullptr));
    }

    bool is_true() const { return op == llvm::CmpInst::FCMP_TRUE; }
    bool is_false() const { return op == llvm::CmpInst::FCMP_FALSE; }

    PurityCondition negate() const {
      return {llvm::CmpInst::getInversePredicate(op), lhs, rhs};
    }

    // IDEA: Use operator| for join (and operator& for meet, if needed),
    // unless it's confusing
    PurityCondition operator&(const PurityCondition &other) const {
      if (other.is_true() || *this == other) return *this;
      if (is_true()) return other;
      return false;
    }
    PurityCondition &operator&=(const PurityCondition &other) {
      // if (other.is_true() || *this == other) return *this;
      // if (is_true()) return *this = other;
      // op = llvm::CmpInst::FCMP_FALSE;
      // lhs = rhs = nullptr;
      // return *this;
      return *this = (*this & other);
    }

    PurityCondition operator|(const PurityCondition &other) const {
      if (other.is_false()) return *this;
      if (is_false()) return other;
      if (lhs == other.lhs && rhs == other.rhs &&
          /* Maybe this can be made more precise. F.ex. <= | >= is also
           * true. There might be such a check in LLVM already. */
          llvm::CmpInst::getInversePredicate(op) == other.op) {
        return true;
      }
      /* XXX: We have to underapproximate :( */
      if (other.is_true()) return other;
      else return *this;
    }

    bool operator!=(const PurityCondition &other) const { return !(*this == other); }
    bool operator==(const PurityCondition &other) const {
      assert(!(is_true() || is_false()) || (lhs == nullptr && rhs == nullptr));
      return lhs == other.lhs && rhs == other.rhs && op == other.op;
    }
    bool operator <(const PurityCondition &other) const {
      if (other.is_true() && !is_true()) return true;
      if (is_false() && !other.is_false()) return true;
      return false;
    }
  };
  typedef std::unordered_map<const llvm::BasicBlock*,PurityCondition> PurityConditions;

  PurityCondition getIn(const llvm::Loop *L, PurityConditions &conds,
                        const llvm::BasicBlock *BB) {
    if (BB == L->getHeader()) return true;
    return conds[BB];
  }

  PurityCondition computeOut(const llvm::Loop *L, PurityConditions &conds,
                             const llvm::BasicBlock *BB) {
    if (auto *branch = llvm::dyn_cast<llvm::BranchInst>(BB->getTerminator())) {
      if (auto *cmp = llvm::dyn_cast_or_null<llvm::CmpInst>
          (branch->isConditional() ? branch->getCondition() : nullptr)) {
        PurityCondition trueIn = getIn(L, conds, branch->getSuccessor(0));
        PurityCondition falseIn = getIn(L, conds, branch->getSuccessor(1));
        if (trueIn == falseIn) return trueIn;
        // If the operands are in the loop, we can check them for
        // purity; if not, the condition should just be false. That way,
        // we won't waste good conditions in the overapproximations
        PurityCondition cmpCond(cmp->getPredicate(), cmp->getOperand(0), cmp->getOperand(1));
        // if (trueIn.is_true()) return falseIn | cmpCond;
        // if (falseIn.is_true()) return trueIn | cmpCond.negate();
        return (falseIn | cmpCond) & (trueIn | cmpCond.negate());
      }
    }

    /* Generic implementation; no concern for branch conditions */
    PurityCondition cond;
    for (const llvm::BasicBlock *s : llvm::successors(BB)) {
      cond &= conds[s];
    }
    return cond;
  }

  /* We should probably calculate this once and cache it */
  /* It also needs to be path-sensitive; a value might escape only on
   * the non-pure path.
   */
  bool escapesLoop(const llvm::Loop *L, const llvm::Value *Value) {
    llvm::SmallPtrSet<const llvm::Value*, 10> tried;
    llvm::SmallVector<const llvm::Value*, 4> stack{Value};
    while(stack.size()) {
      const llvm::Value *V = stack.back(); stack.pop_back();
      if (const llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(V)) {
        if (!L->contains(I->getParent())) return true;
      }
      if (llvm::isa<llvm::ReturnInst>(V)) return true; // XXX: more cases?
      tried.insert(V);
      for (const llvm::Value *U : V->users()) {
        if (tried.count(U)) continue;
        stack.push_back(U);
      }
    }
    return false;
  }

  PurityCondition instructionPurity(llvm::Loop *L, const llvm::Instruction &I) {
    if (!I.mayReadOrWriteMemory()
        && llvm::isSafeToSpeculativelyExecute(&I)) return true;

    if (const llvm::LoadInst *Ld = llvm::dyn_cast<llvm::LoadInst>(&I)) {
      /* No-segfaulting */
      if ((llvm::isa<llvm::GlobalValue>(Ld->getPointerOperand())
           || llvm::isa<llvm::AllocaInst>(Ld->getPointerOperand()))
          && !escapesLoop(L, Ld)) {
        return true;
      }
    }
    if (!I.mayWriteToMemory() && llvm::isSafeToSpeculativelyExecute(&I)) {
      llvm::dbgs() << "Wow, a safe-to-speculate loading inst: " << I << "\n";
      /* Check if we leak the value */
      if (escapesLoop(L, &I))
        return true;
    }
    /* XXX: Do me */

    return false;
  }

  PurityConditions analyseLoop(llvm::Loop *L) {
    PurityConditions conds;
    const auto &blocks = L->getBlocks();
    bool changed;
    do {
      changed = false;
      // Assume it's in reverse postorder, or some suitable order
      for (auto it = blocks.rbegin(); it != blocks.rend(); ++it) {
        const llvm::BasicBlock *BB = *it;
        PurityCondition cond = computeOut(L, conds, BB);
        /* Skip the terminator */
        for (auto it = BB->rbegin(); ++it != BB->rend();) {
          cond &= instructionPurity(L, *it);
        }
        if (conds[BB] != cond) {
          assert(cond < conds[BB]);
          changed = true;
          conds[BB] = cond;
        }
      }
    } while(changed);
    return conds;
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

  llvm::Instruction *findUserLocation(llvm::User *U) {
    llvm::SmallPtrSet<llvm::User*, 16> Set;
    llvm::Instruction *I = maybeFindUserLocation(U, Set);
    if (!I) {
      llvm::dbgs() << "User " << *U << " has no location!\n";
    }
    assert(I);
    return I;
  }

  llvm::Instruction *findInsertionPoint(llvm::Loop *L,
                                        const llvm::DominatorTree &DT,
                                        const PurityCondition &cond) {
    if (llvm::Instruction *LHS = maybeFindUserLocationOrNull
        (llvm::dyn_cast<llvm::User>(cond.lhs))) {
      if (llvm::Instruction *RHS = maybeFindUserLocationOrNull
          (llvm::dyn_cast<llvm::User>(cond.rhs))) {
        if (DT.dominates(LHS, RHS)) return RHS->getNextNode();
        if (DT.dominates(RHS, LHS)) return LHS->getNextNode();
        /* uh oh, hard case */
        assert(false && "Implement me");
      } else {
        return LHS->getNextNode();
      }
    } else if (llvm::Instruction *RHS = maybeFindUserLocationOrNull
               (llvm::dyn_cast<llvm::User>(cond.rhs))) {
      return findUserLocation(RHS);
    }

    return &*L->getHeader()->getFirstInsertionPt();
  }
}

void PartialLoopPurityPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const{
  AU.addRequired<llvm::LLVM_DOMINATOR_TREE_PASS>();
  AU.addRequired<DeclareAssumePass>();
  AU.addPreserved<DeclareAssumePass>();
}

bool PartialLoopPurityPass::runOnLoop(llvm::Loop *L, llvm::LPPassManager &LPM){
  llvm::dbgs() << "Analysing " << L->getHeader()->getParent()->getName() << ":\n";
  llvm::dbgs() << *L->getHeader()->getParent();
  const llvm::DominatorTree &DT
    = getAnalysis<llvm::LLVM_DOMINATOR_TREE_PASS>().getDomTree();
  assert(!DominatorTree);
  DominatorTree = &DT;
  PurityConditions conditions = analyseLoop(L);
  PurityCondition headerCond = conditions[L->getHeader()];
  if (headerCond.is_false()) {
    llvm::dbgs() << "Loop " << L->getHeader()->getParent()->getName() << ":"
                 << *L << " isn't pure\n";
    DominatorTree = nullptr;
    return false;
  } else {
    llvm::dbgs() << "Loop " << L->getHeader()->getParent()->getName() << ":"
                 << *L << ": ";
    if (headerCond.is_true()) llvm::dbgs() << "true\n";
    else {
      llvm::dbgs() << *headerCond.lhs << " " << headerCond.op << " "
                   << *headerCond.rhs << "\n";
    }
  }

  if (headerCond.is_true()) {
    /* Insert assume(false); at the beginning of the header */
  }
  llvm::Instruction *I = findInsertionPoint(L, DT, headerCond);
  llvm::dbgs() << "Insertion point: " << *I << "\n";
  llvm::CmpInst *CmpI = llvm::ICmpInst::Create
    (llvm::Instruction::OtherOps::ICmp,
     llvm::CmpInst::getInversePredicate(headerCond.op),
     headerCond.lhs, headerCond.rhs, "negated.pp.cond", I);
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

  llvm::dbgs() << "Rewritten:\n";
  llvm::dbgs() << *L->getHeader()->getParent();
  assert(!llvm::verifyFunction(*L->getHeader()->getParent(), &llvm::dbgs()));

  DominatorTree = nullptr;
  return true;
}

char PartialLoopPurityPass::ID = 0;
static llvm::RegisterPass<PartialLoopPurityPass> X
("partial-loop-purity",
 "Bound pure and partially pure loops with __VERIFIER_assumes.");
