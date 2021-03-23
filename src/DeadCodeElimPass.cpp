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

#include <llvm/IR/ValueMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/Analysis/ValueTracking.h>

#include "DeadCodeElimPass.h"

void DeadCodeElimPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const{
  AU.setPreservesCFG();
}

namespace {
  typedef llvm::SmallPtrSet<llvm::Value*, 4> UseSet;
  typedef llvm::ValueMap<llvm::BasicBlock*, UseSet> UseSets;

  bool unsafeToDelete(const llvm::Instruction &I) {
    return I.mayReadOrWriteMemory()
      || !I.isSafeToRemove()
      || !llvm::isSafeToSpeculativelyExecute(&I)
      || I.isTerminator();
  }

  UseSet out(UseSets &in, llvm::BasicBlock &BB) {
    UseSet use;
    for (auto it = pred_begin(&BB); it != pred_end(&BB); ++it) {
      auto &out1 = in[*it];
      use.insert(out1.begin(), out1.end());
    }
    return use;
  }

  void computeUseSets(UseSet &use, llvm::Function &F) {
    size_t old_size;
    do {
      old_size = use.size();
      auto &BBL = F.getBasicBlockList();
      for (auto BBI = BBL.rbegin(); BBI != BBL.rend(); ++BBI) {
        assert(BBI->rbegin()->isTerminator());
        assert(unsafeToDelete(*BBI->rbegin()));
        for (auto it = BBI->rbegin(); it != BBI->rend(); ++it) {
          llvm::Instruction &I = *it;
          if (unsafeToDelete(I) || use.count(&I)) {
            use.insert(I.op_begin(), I.op_end());
          }
        }
      }
    } while(use.size() != old_size);
  }
}

bool DeadCodeElimPass::runOnFunction(llvm::Function &F) {
  size_t deleted = 0;
  UseSet use;
  computeUseSets(use, F);

  auto &BBL = F.getBasicBlockList();
  for (auto BBI = BBL.rbegin(); BBI != BBL.rend(); ++BBI) {
    for (auto it = BBI->end(); it != BBI->begin();) {
      llvm::Instruction &I = *--it;
      if (unsafeToDelete(I) || use.count(&I)) {
      } else {
        it = I.eraseFromParent();
        ++deleted;
      }
    }
  }

  return deleted != 0;
}

char DeadCodeElimPass::ID = 0;
static llvm::RegisterPass<DeadCodeElimPass> X("nidhugg-dce","Do SMC-safe dead code elimination.");
