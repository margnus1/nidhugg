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
#include <llvm/IR/Constants.h>
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

  std::uint_fast8_t icmpop_to_bits(llvm::CmpInst::Predicate pred) {
    using llvm::CmpInst;
    assert(pred >= CmpInst::FIRST_ICMP_PREDICATE
           && pred <= CmpInst::LAST_ICMP_PREDICATE);
    switch(pred) {
    case CmpInst::ICMP_SGT: return 0b00010;
    case CmpInst::ICMP_UGT: return 0b00001;
    case CmpInst::ICMP_SGE: return 0b00110;
    case CmpInst::ICMP_UGE: return 0b00101;
    case CmpInst::ICMP_EQ:  return 0b00100;
    case CmpInst::ICMP_NE:  return 0b11011;
    case CmpInst::ICMP_SLE: return 0b01100;
    case CmpInst::ICMP_ULE: return 0b10100;
    case CmpInst::ICMP_SLT: return 0b01000;
    case CmpInst::ICMP_ULT: return 0b10000;
    default: abort();
    }
  }

  llvm::CmpInst::Predicate bits_to_icmpop(std::uint_fast8_t bits) {
    using llvm::CmpInst;
    if ((bits & 0b01110) == 0b01110) return CmpInst::FCMP_TRUE; // Not expected to happen
    if ((bits & 0b10101) == 0b10101) return CmpInst::FCMP_TRUE; // Not expected to happen
    if ((bits & 0b01100) == 0b01100) return CmpInst::ICMP_SLE;
    if ((bits & 0b00110) == 0b00110) return CmpInst::ICMP_SGE;
    if ((bits & 0b10100) == 0b10100) return CmpInst::ICMP_ULE;
    if ((bits & 0b00101) == 0b00101) return CmpInst::ICMP_UGE;
    if ((bits & 0b01000) == 0b01000) return CmpInst::ICMP_SLT;
    if ((bits & 0b00010) == 0b00010) return CmpInst::ICMP_SGT;
    if ((bits & 0b10000) == 0b10000) return CmpInst::ICMP_ULT;
    if ((bits & 0b00001) == 0b00001) return CmpInst::ICMP_UGT;
    if ((bits & 0b01010) == 0b01010) return CmpInst::ICMP_NE;
    if ((bits & 0b10001) == 0b10001) return CmpInst::ICMP_NE;
    if ((bits & 0b00100) == 0b00100) return CmpInst::ICMP_EQ;
    return CmpInst::FCMP_FALSE;
  }

  bool check_predicate_satisfaction(const llvm::APInt &lhs,
                                    llvm::CmpInst::Predicate pred,
                                    const llvm::APInt &rhs) {
    using llvm::CmpInst;
    assert(pred >= CmpInst::FIRST_ICMP_PREDICATE
           && pred <= CmpInst::LAST_ICMP_PREDICATE);
    switch(pred) {
    case CmpInst::ICMP_SGT: return lhs.sgt(rhs);
    case CmpInst::ICMP_UGT: return lhs.ugt(rhs);
    case CmpInst::ICMP_SGE: return lhs.sge(rhs);
    case CmpInst::ICMP_UGE: return lhs.uge(rhs);
    case CmpInst::ICMP_EQ:  return lhs.eq (rhs);
    case CmpInst::ICMP_NE:  return lhs.ne (rhs);
    case CmpInst::ICMP_SLE: return lhs.sle(rhs);
    case CmpInst::ICMP_ULE: return lhs.ule(rhs);
    case CmpInst::ICMP_SLT: return lhs.slt(rhs);
    case CmpInst::ICMP_ULT: return lhs.ult(rhs);
    default: abort();
    }
  }

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

      /* A BinaryPredicate must be normalised after direct modification of its members. */
      void normalise() {
        if (op == llvm::CmpInst::FCMP_TRUE || op == llvm::CmpInst::FCMP_FALSE) {
          lhs = rhs = nullptr;
        } else {
          assert(lhs && rhs);
        }
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

      BinaryPredicate swap() const {
        return {llvm::CmpInst::getSwappedPredicate(op), rhs, lhs};
      }

      // IDEA: Use operator| for join (and operator& for meet, if needed),
      // unless it's confusing
      BinaryPredicate operator&(const BinaryPredicate &other) const {
        if (other.is_true() || *this == other) return *this;
        if (is_true()) return other;

        using llvm::CmpInst;
        BinaryPredicate res = *this;
        BinaryPredicate o(other);
        if (res.rhs == o.lhs || res.rhs == o.rhs) res = swap();
        if (res.lhs == o.lhs || res.lhs == o.rhs) {
          if (res.lhs != o.lhs) o = o.swap();
          if (res.rhs == o.rhs) {
            if (res.op >= CmpInst::FIRST_FCMP_PREDICATE
                && res.op <= CmpInst::LAST_FCMP_PREDICATE) {
              assert(o.op >= CmpInst::FIRST_FCMP_PREDICATE
                     && o.op <= CmpInst::LAST_FCMP_PREDICATE);
              res.op = CmpInst::Predicate(res.op & o.op);
            } else {
              assert(res.op >= CmpInst::FIRST_ICMP_PREDICATE
                     && res.op <= CmpInst::LAST_ICMP_PREDICATE
                     && o.op >= CmpInst::FIRST_ICMP_PREDICATE
                     && o.op <= CmpInst::LAST_ICMP_PREDICATE);
              res.op = bits_to_icmpop(icmpop_to_bits(res.op) & icmpop_to_bits(o.op));
            }
            res.normalise();
            return res;
          }
          if (llvm::isa<llvm::ConstantInt>(res.rhs) && llvm::isa<llvm::ConstantInt>(o.rhs)) {
            assert((llvm::cast<llvm::ConstantInt>(res.rhs)->getValue()
                    != llvm::cast<llvm::ConstantInt>(o.rhs)->getValue()));
            if (res.op == CmpInst::ICMP_EQ || o.op == CmpInst::ICMP_EQ) {
              if (res.op != CmpInst::ICMP_EQ) std::swap(o, res);
              const llvm::APInt &RR = llvm::cast<llvm::ConstantInt>(res.rhs)->getValue();
              const llvm::APInt &OR = llvm::cast<llvm::ConstantInt>(o.rhs)->getValue();
              if (check_predicate_satisfaction(RR, o.op, OR)) {
                return res;
              } else {
                return false;
              }
            }
            if (res.op == CmpInst::ICMP_NE || o.op == CmpInst::ICMP_NE) {
              if (o.op != CmpInst::ICMP_NE) std::swap(o, res);
              const llvm::APInt &RR = llvm::cast<llvm::ConstantInt>(res.rhs)->getValue();
              const llvm::APInt &OR = llvm::cast<llvm::ConstantInt>(o.rhs)->getValue();
              if (check_predicate_satisfaction(OR, res.op, RR)) {
                return false; /* Possible to refine: we'd have to
                               * exclude OR from res somehow */
              } else {
                return res;
              }
            }
            {
              const llvm::APInt &RR = llvm::cast<llvm::ConstantInt>(res.rhs)->getValue();
              const llvm::APInt &OR = llvm::cast<llvm::ConstantInt>(o.rhs)->getValue();
              if (res.op == CmpInst::ICMP_SGE && (o.op == CmpInst::ICMP_SGE
                                                  || o.op == CmpInst::ICMP_SGT)) {
                if (RR.sge(OR)) return o;
                else return res;
              }
              if (res.op == CmpInst::ICMP_UGE && (o.op == CmpInst::ICMP_UGE
                                                  || o.op == CmpInst::ICMP_UGT)) {
                if (RR.uge(OR)) return o;
                else return res;
              }
              if (res.op == CmpInst::ICMP_SGT && (o.op == CmpInst::ICMP_SGE
                                                  || o.op == CmpInst::ICMP_SGT)) {
                if (RR.sgt(OR)) return o;
                else return res;
              }
              if (res.op == CmpInst::ICMP_UGT && (o.op == CmpInst::ICMP_UGE
                                                  || o.op == CmpInst::ICMP_UGT)) {
                if (RR.ugt(OR)) return o;
                else return res;
              }
              if (res.op == CmpInst::ICMP_SLE && (o.op == CmpInst::ICMP_SLE
                                                  || o.op == CmpInst::ICMP_SLT)) {
                if (RR.sle(OR)) return o;
                else return res;
              }
              if (res.op == CmpInst::ICMP_ULE && (o.op == CmpInst::ICMP_ULE
                                                  || o.op == CmpInst::ICMP_ULT)) {
                if (RR.ule(OR)) return o;
                else return res;
              }
              if (res.op == CmpInst::ICMP_SLT && (o.op == CmpInst::ICMP_SLE
                                                  || o.op == CmpInst::ICMP_SLT)) {
                if (RR.slt(OR)) return o;
                else return res;
              }
              if (res.op == CmpInst::ICMP_ULT && (o.op == CmpInst::ICMP_ULE
                                                  || o.op == CmpInst::ICMP_ULT)) {
                if (RR.ult(OR)) return o;
                else return res;
              }
            }
          }
        }

        return false;
      }
      BinaryPredicate &operator&=(const BinaryPredicate &other) {
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
    PurityCondition(BinaryPredicate pred, llvm::Instruction *insertion_point = nullptr)
      : pred(std::move(pred)), insertion_point(pred.is_false() ? nullptr : insertion_point) {}
    PurityCondition(llvm::CmpInst::Predicate op, llvm::Value *lhs,
                    llvm::Value *rhs) : pred(op, lhs, rhs) {}
    // PurityCondition(BinaryPredicate pred, llvm::Instruction *insertion_point)
    //   : pred(std::move(pred)), insertion_point(insertion_point) {}

    /* A PurityCondition must be normalised after direct modification of its members. */
    void normalise() {
      pred.normalise();
      if (pred.is_false()) insertion_point = nullptr;
    }

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
        llvm::dbgs() << "Meeting insertion points general case not implemented:\n";
        llvm::dbgs() << "    " << *insertion_point << "\n"
                     << " and" << *other.insertion_point << "\n";
        assert(false);
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
    case ICmpInst::BAD_ICMP_PREDICATE:
    case FCmpInst::BAD_FCMP_PREDICATE:
      (void)0; // fallthrough
    }
    llvm::dbgs() << "Predicate " << pred << " unknown!\n";
    assert(false && "unknown predicate"); abort();
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
      os << " before " << *cond.insertion_point;
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
      if (llvm::CmpInst::isFalseWhenEqual(cond.pred.op)) cond.pred = false;
      if (llvm::CmpInst::isTrueWhenEqual(cond.pred.op))  cond.pred = true;
    }
    if (llvm::ConstantInt *LHS = llvm::dyn_cast_or_null<llvm::ConstantInt>(cond.pred.lhs)) {
      if (llvm::ConstantInt *RHS = llvm::dyn_cast_or_null<llvm::ConstantInt>(cond.pred.rhs)) {
        if (check_predicate_satisfaction(LHS->getValue(), cond.pred.op, RHS->getValue())) {
          cond.pred = true;
        } else  {
          cond = false;
        }
      }
    }

    cond.normalise();
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
    in.normalise();
    collapseTautologies(in);
    return in;
  }

  PurityCondition computeOut(const llvm::Loop *L, PurityConditions &conds,
                             const llvm::BasicBlock *BB) {
    if (auto *branch = llvm::dyn_cast<llvm::BranchInst>(BB->getTerminator())) {
      if (auto *cmp = llvm::dyn_cast_or_null<llvm::CmpInst>
          (branch->isConditional() ? branch->getCondition() : nullptr)) {
        llvm::BasicBlock *trueSucc = branch->getSuccessor(0);
        llvm::BasicBlock *falseSucc = branch->getSuccessor(1);
        PurityCondition trueIn = getIn(L, conds, BB, trueSucc);
        PurityCondition falseIn = getIn(L, conds, BB, falseSucc);
        if (trueIn == falseIn) return trueIn;
        // If the operands are in the loop, we can check them for
        // purity; if not, the condition should just be false. That way,
        // we won't waste good conditions in the overapproximations
        PurityCondition cmpCond(cmp->getPredicate(), cmp->getOperand(0), cmp->getOperand(1));
        if (!L->contains(trueSucc)) {
          assert(trueIn.is_false());
          if (falseIn.is_true()) return cmpCond.negate();
          return falseIn & PurityCondition(true, &*falseSucc->getFirstInsertionPt());
        }
        if (!L->contains(falseSucc)) {
          assert(falseIn.is_false());
          if (trueIn.is_true()) return cmpCond;
          return trueIn & PurityCondition(true, &*trueSucc->getFirstInsertionPt());
        }
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

  bool isSafeToLoadFromPointer(const llvm::Value *V) {
    return llvm::isa<llvm::GlobalValue>(V)
      || llvm::isa<llvm::AllocaInst>(V);
  }

  PurityCondition instructionPurity(llvm::Loop *L, llvm::Instruction &I) {
    if (!I.mayReadOrWriteMemory()
        && llvm::isSafeToSpeculativelyExecute(&I)) return true;
    if (llvm::isa<llvm::PHINode>(I)) return true;

    if (const llvm::LoadInst *Ld = llvm::dyn_cast<llvm::LoadInst>(&I)) {
      /* No-segfaulting */
      if (isSafeToLoadFromPointer(Ld->getPointerOperand())) {
        return true;
      } else {
        return PurityCondition(true, I.getNextNode());
      }
    }
    if (!I.mayWriteToMemory()) {
      if (llvm::isSafeToSpeculativelyExecute(&I)) {
        llvm::dbgs() << "Wow, a safe-to-speculate loading inst: " << I << "\n";
        return true;
      } else {
        return PurityCondition(true, I.getNextNode());
      }
    }
    if (llvm::AtomicRMWInst *RMW = llvm::dyn_cast<llvm::AtomicRMWInst>(&I)) {
      PurityCondition::BinaryPredicate pred(false);
      llvm::Value *arg = RMW->getValOperand();
      switch (RMW->getOperation()) {
      case llvm::AtomicRMWInst::BinOp::Add:
      case llvm::AtomicRMWInst::BinOp::Or:
      case llvm::AtomicRMWInst::BinOp::Sub:
      case llvm::AtomicRMWInst::BinOp::UMax:
      case llvm::AtomicRMWInst::BinOp::Xor:
        /* arg == 0 */
        pred = {llvm::CmpInst::ICMP_EQ, arg,
          llvm::ConstantInt::get(RMW->getType(), 0)};
        break;
      case llvm::AtomicRMWInst::BinOp::And:
      case llvm::AtomicRMWInst::BinOp::UMin:
        /* arg == 0b111...1 */
        pred = {llvm::CmpInst::ICMP_EQ, arg,
          llvm::ConstantInt::getAllOnesValue(RMW->getType())};
        break;
      case llvm::AtomicRMWInst::BinOp::Xchg:
        /* ret == arg */
        pred = {llvm::CmpInst::ICMP_EQ, &I, arg};
        break;
      }
      PurityCondition ret;
      if (isSafeToLoadFromPointer(RMW->getPointerOperand())) {
        ret = PurityCondition(pred);
      } else {
        ret = PurityCondition(pred, I.getNextNode());
      }
      collapseTautologies(ret);
      return ret;
    }

    /* Extension: We do not yet handle when the return value of the cmpxchg is used for  */
    if (llvm::AtomicCmpXchgInst *CX = llvm::dyn_cast<llvm::AtomicCmpXchgInst>(&I)) {
      /* Try to find a ExtractValue instruction that extracts the
       * success bit */
      llvm::ExtractValueInst *success = nullptr;
      for (llvm::User *U : CX->users()) {
        if (llvm::ExtractValueInst *EV = llvm::dyn_cast<llvm::ExtractValueInst>(U)) {
          if (EV->getNumIndices() == 1 && EV->idx_begin()[0] == 1) {
            success = EV;
            break;
          }
        }
      }
      if (success) {
        PurityCondition::BinaryPredicate pred
          (llvm::CmpInst::ICMP_EQ, success,
           llvm::ConstantInt::getFalse(CX->getContext()));
        if (isSafeToLoadFromPointer(CX->getPointerOperand())) {
          return PurityCondition(pred);
        } else {
          return PurityCondition(pred, I.getNextNode());
        }
      }
    }
    /* Extension point: We could add more instructions here */

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
          (llvm::dyn_cast_or_null<llvm::User>(cond.pred.lhs))) {
        if (llvm::Instruction *RHS = maybeFindUserLocationOrNull
            (llvm::dyn_cast_or_null<llvm::User>(cond.pred.rhs))) {
          if (DT.dominates(LHS, IPT) &&
              DT.dominates(RHS, IPT)) return IPT;
          if (dominates_or_equals(DT, IPT, RHS->getNextNode()) &&
              dominates_or_equals(DT, LHS, RHS)) return RHS->getNextNode();
          if (dominates_or_equals(DT, IPT, LHS->getNextNode()) &&
              dominates_or_equals(DT, RHS, LHS)) return LHS->getNextNode();
          /* uh oh, hard case */
          assert(false && "Implement me"); abort();
        } else {
          if (DT.dominates(LHS, IPT)) return IPT;
          if (dominates_or_equals(DT, IPT, LHS->getNextNode())) return LHS->getNextNode();
          /* uh oh, hard case */
          assert(false && "Implement me"); abort();
        }
      } else if (llvm::Instruction *RHS = maybeFindUserLocationOrNull
            (llvm::dyn_cast_or_null<llvm::User>(cond.pred.rhs))) {
          if (DT.dominates(LHS, IPT)) return IPT;
          if (dominates_or_equals(DT, IPT, LHS->getNextNode())) return LHS->getNextNode();
          /* uh oh, hard case */
          assert(false && "Implement me"); abort();
      } else {
        return IPT;
      }
    } else {
      if (llvm::Instruction *LHS = maybeFindUserLocationOrNull
          (llvm::dyn_cast_or_null<llvm::User>(cond.pred.lhs))) {
        if (llvm::Instruction *RHS = maybeFindUserLocationOrNull
            (llvm::dyn_cast_or_null<llvm::User>(cond.pred.rhs))) {
          if (dominates_or_equals(DT, LHS, RHS)) return RHS->getNextNode();
          if (dominates_or_equals(DT, RHS, LHS)) return LHS->getNextNode();
          /* uh oh, hard case */
          assert(false && "Implement me"); abort();
        } else {
          return LHS->getNextNode();
        }
      } else if (llvm::Instruction *RHS = maybeFindUserLocationOrNull
                 (llvm::dyn_cast_or_null<llvm::User>(cond.pred.rhs))) {
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

  llvm::Instruction *I = findInsertionPoint(L, DT, headerCond);
  llvm::dbgs() << " Insertion point: " << *I << "\n";
  llvm::Value *Cond;
  if (headerCond.pred.is_true()) {
    Cond = llvm::ConstantInt::getTrue(L->getHeader()->getContext());
  } else {
    Cond = llvm::ICmpInst::Create
      (getPredicateOpcode(headerCond.pred.op),
       llvm::CmpInst::getInversePredicate(headerCond.pred.op),
       headerCond.pred.lhs, headerCond.pred.rhs, "negated.pp.cond", I);
  }
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
