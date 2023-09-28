//===- AutoMode.cpp ------------------------------------- ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//
//
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Transforms/Khaos/Utils.h"

#define DEBUG_TYPE "automode"

std::map<Function *, int> complexityMap;
int getCFGComplexity(Function *f) {
  auto iter = complexityMap.find(f);
  if (iter != complexityMap.end())
    return iter->second;
  int complexity = 2;
  for (auto &BB : *f) {
    int edge = 0;
    for (auto succ : successors(&BB))
      edge++;
    complexity += edge - 1;
  }
  complexityMap[f] = complexity;
  return complexity;
}

bool compareFunctionSize(Function *f1, Function *f2) {
  return (f1->getBasicBlockList().size() * getCFGComplexity(f1) <
          f2->getBasicBlockList().size() * getCFGComplexity(f2));
} // ascending

namespace {
struct AutoModePass : public ModulePass {
  static char ID; // Pass identification, replacement for typeid

  AutoModePass() : ModulePass(ID) {
    initializeAutoModePassPass(*PassRegistry::getPassRegistry());
  }
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<BlockFrequencyInfoWrapperPass>();
    AU.addRequired<BranchProbabilityInfoWrapperPass>();
    AU.setPreservesAll();
  }
  bool runOnModule(Module &M) override;
};

} // namespace

char AutoModePass::ID = 0;

bool AutoModePass::runOnModule(Module &M) {
  
  int cntFunc = M.getFunctionList().size();
  int cntFiss = 0, cntFus = 0, cntIntra = 0;
  for (auto &F : M) {
    if (getCFGComplexity(&F) <= 3) {
      F.setAutoModeFusion(true);
      cntFus++;
    } else if (getCFGComplexity(&F) <= 6) {
      F.setAutoModeIntra(true);
      cntIntra++;
    } else {
      F.setAutoModeFission(true);
      cntFiss++;
    }
  }
  outs() << "Auto Mode Statistics: Fusion: " << cntFus << "/" << cntFunc << 
                                ", Fission: " << cntFiss << "/" <<  cntFunc <<
                                ", Intra: " << cntIntra << "/" << cntFunc << "\n";
  return false;
}

// static RegisterPass<AutoModePass> X("automode", "Auto Mode Pass");
INITIALIZE_PASS_BEGIN(AutoModePass, "AutoModePass", "AutoModePass Pass", false,
                      false)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(BlockFrequencyInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_END(AutoModePass, "AutoModePass", "AutoModePass Pass", false,
                    false)

ModulePass *llvm::createAutoModePass() { return new AutoModePass(); }
