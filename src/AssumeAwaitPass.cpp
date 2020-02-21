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
#if defined(HAVE_LLVM_SUPPORT_CALLSITE_H)
#include <llvm/Support/CallSite.h>
#elif defined(HAVE_LLVM_IR_CALLSITE_H)
#include <llvm/IR/CallSite.h>
#endif
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Config/llvm-config.h>

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
        llvm::Type *voidTy = llvm::Type::getVoidTy(M.getContext());
        llvm::Type *i8Ty = llvm::Type::getInt8Ty(M.getContext());
        llvm::Type *ixTy = llvm::IntegerType::get(M.getContext(),sizes[i]);
        llvm::Type *ixPTy = llvm::PointerType::getUnqual(ixTy);
        loadAwaitTy = llvm::FunctionType::get(voidTy,{ixPTy, i8Ty, ixTy},false);
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
  return false;
}

char AssumeAwaitPass::ID = 0;
static llvm::RegisterPass<AssumeAwaitPass> X("assume-await","Replace simple __VERIFIER_assumes with .");
