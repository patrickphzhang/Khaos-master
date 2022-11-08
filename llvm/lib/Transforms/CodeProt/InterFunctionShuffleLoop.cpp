//===- InterFunctionShuffleLoop.cpp - Extract each loop into a new function ----------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// A pass wrapper around the ExtractLoop() scalar transformation to extract each
// top-level loop into its own new function. If the loop is the ONLY loop in a
// given function, it is not touched. This is a pass most useful for debugging
// via bugpoint.
//
//===----------------------------------------------------------------------===//


#include "llvm/Transforms/CodeProt/Utils.h"
#include "llvm/Transforms/CodeProt/CPCodeExtractor.h"

#define DEBUG_TYPE "loop"

STATISTIC(NumExtracted, "Number of loops extracted by InterFunctionShuffle");

namespace {
  struct InterFunctionShuffleLoop : public LoopPass {
    static char ID; // Pass identification, replacement for typeid
    const string ProtName = PROTNAME_INTERSHUFFLE;
    const int ProtRatio = RatioInterShuffle;
    unsigned NumLoops;

    explicit InterFunctionShuffleLoop(unsigned numLoops = ~0)
      : LoopPass(ID), NumLoops(numLoops) {
        initializeInterFunctionShuffleLoopPass(*PassRegistry::getPassRegistry());
      }

    bool runOnLoop(Loop *L, LPPassManager &) override;

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequiredID(BreakCriticalEdgesID);
      AU.addRequiredID(LoopSimplifyID);
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<LoopInfoWrapperPass>();
      AU.addUsedIfAvailable<AssumptionCacheTracker>();
    }
  };
}

char InterFunctionShuffleLoop::ID = 0;
INITIALIZE_PASS_BEGIN(InterFunctionShuffleLoop, "intershuffleloop",
                      "InterFunctionShuffleLoop Pass", false, false)
INITIALIZE_PASS_DEPENDENCY(BreakCriticalEdges)
INITIALIZE_PASS_DEPENDENCY(LoopSimplify)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_END(InterFunctionShuffleLoop, "intershuffleloop",
                    "InterFunctionShuffleLoop Pass", false, false)

namespace {
  /// InterFunctionShuffleLoopMulti - For bugpoint.
  struct InterFunctionShuffleLoopMulti : public InterFunctionShuffleLoop {
    static char ID; // Pass identification, replacement for typeid
    InterFunctionShuffleLoopMulti() : InterFunctionShuffleLoop(10) {}
  };
} // End anonymous namespace

char InterFunctionShuffleLoopMulti::ID = 0;
INITIALIZE_PASS(InterFunctionShuffleLoopMulti, "intershuffleloopmulti",
                "InterFunctionShuffleLoopMulti Pass", false, false)

// createInterFunctionShuffleLoopPass - This pass extracts all natural loops from the
// program into a function if it can.
//
Pass *llvm::createInterFunctionShuffleLoopPass() { return new InterFunctionShuffleLoop(); }

bool InterFunctionShuffleLoop::runOnLoop(Loop *L, LPPassManager &LPM) {
  	// return false;
	LLVM_DEBUG(outs() << "InterFunctionShuffleLoop debug!\n");
  Function *F = L->getHeader()->getParent();
  Module *M = F->getParent();
  bool Changed = false;
  bool needProtect = inConfigOrRandom(ProtName, *M, *F, ProtRatio);
  if (needProtect) {
      LLVM_DEBUG(outs() << "func checked: " << F->getName() << "\n");

      if (skipLoop(L))
        return false;

      // Only visit top-level loops.
      if (L->getParentLoop())
        return false;

      // If LoopSimplify form is not available, stay out of trouble.
      if (!L->isLoopSimplifyForm())
        return false;

      if (L->getHeader()->getParent()->isCreatedByCodeProt()) {
        // errs() << "skipping loop\n";
        return false;
      }

      DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
      LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();


      // If there is more than one top-level loop in this function, extract all of
      // the loops. Otherwise there is exactly one top-level loop; in this case if
      // this function is more than a minimal wrapper around the loop, extract
      // the loop.
      bool ShouldExtractLoop = false;

      // Extract the loop if the entry block doesn't branch to the loop header.
      Instruction *EntryTI =
          L->getHeader()->getParent()->getEntryBlock().getTerminator();
      if (!isa<BranchInst>(EntryTI) ||
          !cast<BranchInst>(EntryTI)->isUnconditional() ||
          EntryTI->getSuccessor(0) != L->getHeader()) {
        ShouldExtractLoop = true;
      } else {
        // Check to see if any exits from the loop are more than just return
        // blocks.
        SmallVector<BasicBlock*, 8> ExitBlocks;
        L->getExitBlocks(ExitBlocks);
        for (unsigned i = 0, e = ExitBlocks.size(); i != e; ++i)
          if (!isa<ReturnInst>(ExitBlocks[i]->getTerminator())) {
            ShouldExtractLoop = true;
            break;
          }
      }

      for (auto ib = L->block_begin(), ie = L->block_end(); ib != ie; ib++) {
		    for (Instruction &I : **ib) {
          if (const InvokeInst *II = dyn_cast<InvokeInst>(&I)) {
            ShouldExtractLoop = false;
            break;
          }
        }
        if (!ShouldExtractLoop) break;
      }

      if (ShouldExtractLoop) {
        // We must omit EH pads. EH pads must accompany the invoke
        // instruction. But this would result in a loop in the extracted
        // function. An infinite cycle occurs when it tries to extract that loop as
        // well.
        SmallVector<BasicBlock*, 8> ExitBlocks;
        L->getExitBlocks(ExitBlocks);
        for (unsigned i = 0, e = ExitBlocks.size(); i != e; ++i)
          if (ExitBlocks[i]->isEHPad()) {
            ShouldExtractLoop = false;
            break;
          }
      }

      if (ShouldExtractLoop) {
        if (NumLoops == 0) return Changed;
        --NumLoops;
        AssumptionCache *AC = nullptr;
        if (auto *ACT = getAnalysisIfAvailable<AssumptionCacheTracker>())
          AC = ACT->lookupAssumptionCache(*L->getHeader()->getParent());
        CPCodeExtractor Extractor(DT, *L, false, nullptr, nullptr, AC);
        Function *ExtractedFunc = Extractor.extractCodeRegion();
        if (ExtractedFunc != nullptr) {
          Changed = true;
          // After extraction, the loop is replaced by a function call, so
          // we shouldn't try to run any more loop passes on it.
          LPM.markLoopAsDeleted(*L);
          LI.erase(L);
          LLVM_DEBUG(outs() << "In Inter Shuffle: " << ExtractedFunc->getName() << "\n");
          ExtractedFunc->setCreatedByCodeProt(true);
          ExtractedFunc->setOriginNameLength(F->getName().size());
          // appendToUsed(*M, ExtractedFunc);
          ExtractedFunc->addFnAttr(Attribute::NoInline);
          LLVM_DEBUG(outs() << "Extracted Loop: " << ExtractedFunc->getName() << "\n");
          errs() << "cp extracted loop\n";
        }
        ++NumExtracted;
      }
  } else {
      LLVM_DEBUG(outs() << "func nochecked: " << F->getName() << "\n");
  }
  
  return Changed;
}

// createInterFunctionShuffleLoopMultiPass - This pass extracts one natural loop from the
// program into a function if it can.  This is used by bugpoint.
//
Pass *llvm::createInterFunctionShuffleLoopMultiPass() {
  return new InterFunctionShuffleLoopMulti();
}
