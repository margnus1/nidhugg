/* Copyright (C) 2020 Magnus Lång
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
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Operator.h>
#include <llvm/Config/llvm-config.h>
#include <llvm/Support/Debug.h>

// #include "CheckModule.h"
#include "AssumeAwaitPass.h"
#include "SpinAssumePass.h"
#include "AwaitCond.h"

#ifdef LLVM_HAS_ATTRIBUTELIST
typedef llvm::AttributeList AttributeList;
#else
typedef llvm::AttributeSet AttributeList;
#endif

#ifdef LLVM_HAS_TERMINATORINST
typedef llvm::TerminatorInst TerminatorInst;
#else
typedef llvm::Instruction TerminatorInst;
#endif

void AssumeAwaitPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const{
  AU.setPreservesCFG();
  AU.addRequired<llvm::LLVM_DOMINATOR_TREE_PASS>();
}

unsigned AssumeAwaitPass::sizes[AssumeAwaitPass::no_sizes] = {8,16,32,64};

namespace {
  llvm::Value* getOrInsertFunction(llvm::Module &M, llvm::StringRef Name,
                                   llvm::FunctionType *T, AttributeList AttributeList) {
    return M.getOrInsertFunction(std::move(Name),T,std::move(AttributeList))
#if LLVM_VERSION_MAJOR >= 9
      /* XXX: I will not work with some development versions of 9, I
       * should be replaced/complemented with a configure check.
       */
      .getCallee()
#endif
      ;
  }

  bool is_assume(llvm::CallInst *C) {
    llvm::Function *F = C->getCalledFunction();
    return F && F->getName().str() == "__VERIFIER_assume";
  }

  bool is_true(llvm::Value *v) {
    auto *I = llvm::dyn_cast<llvm::Constant>(v);
    return I && I->isAllOnesValue();
  }

  llvm::ICmpInst *get_condition(llvm::Value *v, bool *negate) {
    if (auto *ret = llvm::dyn_cast<llvm::ICmpInst>(v)) return ret;
    if (auto *op = llvm::dyn_cast<llvm::ZExtOperator>(v))
      return get_condition(op->getOperand(0), negate);
    if (auto *op = llvm::dyn_cast<llvm::Instruction>(v)) {
      if (op->getOpcode() == llvm::Instruction::ZExt) {
        return get_condition(op->getOperand(0), negate);
      } else if(op->getOpcode() == llvm::Instruction::Xor) {
        if (is_true(op->getOperand(0)) || is_true(op->getOperand(1))) {
          *negate ^= true;
          return get_condition(op->getOperand(is_true(op->getOperand(0)) ? 1 : 0), negate);
        }
      }
    }
    return nullptr;
  }

  AwaitCond::Op get_op(llvm::CmpInst::Predicate p) {
    switch(p) {
    case llvm::CmpInst::ICMP_EQ:  return AwaitCond::EQ;
    case llvm::CmpInst::ICMP_NE:  return AwaitCond::NE;
    case llvm::CmpInst::ICMP_UGT: return AwaitCond::UGT;
    case llvm::CmpInst::ICMP_UGE: return AwaitCond::UGE;
    case llvm::CmpInst::ICMP_ULT: return AwaitCond::ULT;
    case llvm::CmpInst::ICMP_ULE: return AwaitCond::ULE;
    case llvm::CmpInst::ICMP_SGT: return AwaitCond::SGT;
    case llvm::CmpInst::ICMP_SGE: return AwaitCond::SGE;
    case llvm::CmpInst::ICMP_SLT: return AwaitCond::SLT;
    case llvm::CmpInst::ICMP_SLE: return AwaitCond::SLE;
    default: return AwaitCond::None;
    }
  }

  std::uint8_t get_mode(llvm::LoadInst *Load) {
    switch (Load->getOrdering()) {
      /* TODO: lift these modes to an enum somewhere */
    case llvm::AtomicOrdering::NotAtomic:
    case llvm::AtomicOrdering::Unordered:
    case llvm::AtomicOrdering::Monotonic:
      return 0; /* Races are bugs */
    case llvm::AtomicOrdering::Acquire:
      return 1; /* Release/Aquire */
    case llvm::AtomicOrdering::SequentiallyConsistent:
      return 2;
    default:
      llvm_unreachable("No other access modes allowed for Loads");
    }
  }

  llvm::LoadInst *is_permissible_load(llvm::Value *V, llvm::BasicBlock *BB) {
    llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(V);
    if (!I || I->getParent() != BB) return nullptr;
    if (auto *Load = llvm::dyn_cast<llvm::LoadInst>(I)) {
      return Load;
    }
    return nullptr;
  }

  bool is_permissible_arg(llvm::DominatorTree &DT, llvm::Value *V, llvm::LoadInst *Load) {
    if (llvm::isa<llvm::Constant>(V)) return true;
    if (llvm::isa<llvm::Argument>(V)) return true;
    if (llvm::Instruction *VI = llvm::dyn_cast<llvm::Instruction>(V))
      return DT.dominates(VI, Load);
    /* TODO: What about operators applied to permissible_arg(s)? */
    return false;
  }

  bool is_safe_intermediary(llvm::Instruction *I) {
    return !I->mayHaveSideEffects();
  }

  bool is_safe_to_rewrite(llvm::LoadInst *Load, llvm::CallInst *Call) {
    assert(Load->getParent() == Call->getParent()
           && "We don't yet implement BB traversal");
    llvm::BasicBlock::iterator li(Load), ci(Call);
    while (--ci != li) {
      if (!is_safe_intermediary(&*ci)) return false;
    }
    return true;
  }
}

bool AssumeAwaitPass::doInitialization(llvm::Module &M){
  bool modified_M = false;
  // CheckModule::check_await(&M);

  for (unsigned i = 0; i < no_sizes; ++i) {
    std::string name = "__VERIFIER_load_await_i" + std::to_string(sizes[i]);
    F_load_await[i] = M.getFunction(name);
    if(!F_load_await[i]){
      llvm::FunctionType *loadAwaitTy;
      {
        llvm::Type *i8Ty = llvm::Type::getInt8Ty(M.getContext());
        llvm::Type *ixTy = llvm::IntegerType::get(M.getContext(),sizes[i]);
        llvm::Type *ixPTy = llvm::PointerType::getUnqual(ixTy);
        loadAwaitTy = llvm::FunctionType::get(ixTy,{ixPTy, i8Ty, ixTy, i8Ty},false);
      }
      AttributeList assumeAttrs =
        AttributeList::get(M.getContext(),AttributeList::FunctionIndex,
                           std::vector<llvm::Attribute::AttrKind>({llvm::Attribute::NoUnwind}));
      F_load_await[i] = getOrInsertFunction(M,name,loadAwaitTy,assumeAttrs);
      modified_M = true;
    }
  }
  return modified_M;
}

bool AssumeAwaitPass::runOnFunction(llvm::Function &F) {
  bool changed = false;

  for (llvm::BasicBlock &BB : F) {
    for (auto it = BB.begin(), end = BB.end(); it != end;) {
      if (tryRewriteAssume(&F, &BB, &*it)) {
        changed = true;
        if (it->use_empty()) it = it->eraseFromParent();
        else ++it;
      } else {
        ++it;
      }
    }
  }

  return changed;
}

bool AssumeAwaitPass::tryRewriteAssume(llvm::Function *F, llvm::BasicBlock *BB, llvm::Instruction *I) const {
  llvm::CallInst *Call = llvm::dyn_cast<llvm::CallInst>(I);
  if (!Call || !is_assume(Call)) return false;
  bool negate = false;
  llvm::ICmpInst *Cond = get_condition(Call->getArgOperand(0), &negate);
  if (!Cond) {
    llvm::dbgs() << "Not rewriting assume in " << F->getName() << ": Could not find condition\n";
    return false;
  }
  bool blame_load;
  for (unsigned load_index = 0; load_index < 2; ++load_index) {
    llvm::LoadInst *Load = is_permissible_load(Cond->getOperand(load_index),BB);
    blame_load = !Load;
    if (!Load) {
      /* Message is printed later, if relevant */
      continue;
    }
    llvm::Value *ArgVal = Cond->getOperand(1-load_index);
    llvm::CmpInst::Predicate pred = Cond->getPredicate();
    if (bool(load_index) ^ negate) pred = llvm::CmpInst::getSwappedPredicate(pred);
    llvm::DominatorTree &DT = getAnalysis<llvm::LLVM_DOMINATOR_TREE_PASS>().getDomTree();
    if (!is_permissible_arg(DT, ArgVal, Load)) {
      llvm::dbgs() << "Not rewriting assume in " << F->getName() << ": RHS not permissible\n";
      continue;
    }
    if (!is_safe_to_rewrite(Load, Call)) {
      llvm::dbgs() << "Not rewriting assume in " << F->getName() << ": Rewrite would be unsafe\n";
      continue;
    }
    AwaitCond::Op op = get_op(pred);
    if (op == AwaitCond::None) {
      llvm::dbgs() << "Not rewriting assume in " << F->getName()
                   << ": Could not convert condition\n";
      continue;
    }
    llvm::Value *AwaitFunction = getLoadAwait(Load->getType());
    if (!AwaitFunction) {
      llvm::dbgs() << "Not rewriting assume in " << F->getName()
                   << ": Bad type " << Load->getType() << "\n";
      continue;
    }
    assert(llvm::isa<llvm::FunctionType>(AwaitFunction->getType()));
    llvm::FunctionType *AwaitFunctionType
        = llvm::cast<llvm::FunctionType>(AwaitFunction->getType());
    llvm::dbgs() << "Wow, replacing " << *Load << " and " << *Call << " in " << F->getName() << "\n";
    llvm::IntegerType *i8Ty = llvm::Type::getInt8Ty(F->getParent()->getContext());
    llvm::ConstantInt *COp = llvm::ConstantInt::get(i8Ty, op);
    llvm::ConstantInt *CMode = llvm::ConstantInt::get(i8Ty, get_mode(Load));
    llvm::Value *Address = Load->getOperand(0);
    llvm::BasicBlock::iterator LI(Load);
    llvm::ReplaceInstWithInst(Load->getParent()->getInstList(), LI,
                              llvm::CallInst::Create(AwaitFunctionType, AwaitFunction, {Address, COp, ArgVal, CMode}));
    return true;
  }
  if (blame_load)
    llvm::dbgs() << "Not rewriting assume in " << F->getName() << ": Could not find load\n";
  return false;
}

llvm::Value *AssumeAwaitPass::getLoadAwait(llvm::Type *t) const {
  if (!t->isIntegerTy()) return nullptr;
  unsigned index;
  switch(t->getIntegerBitWidth()) {
  case 8:  index = 0; break;
  case 16: index = 1; break;
  case 32: index = 2; break;
  case 64: index = 3; break;
  default: return nullptr;
  }
  return F_load_await[index];
}

char AssumeAwaitPass::ID = 0;
static llvm::RegisterPass<AssumeAwaitPass> X("assume-await","Replace simple __VERIFIER_assumes with __VERIFIER_await.");
