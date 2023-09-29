//===- Strip.cpp ------------------------------------- ---------------===//
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

#include "llvm/IR/BasicBlock.h"
#include "llvm/Transforms/Khaos/Utils.h"

#define DEBUG_TYPE "Strip"
namespace {
struct Strip : public ModulePass {
  static char ID; // Pass identification, replacement for typeid

  Strip() : ModulePass(ID) {
    initializeStripPass(*PassRegistry::getPassRegistry());
  }
  bool runOnModule(Module &M) override;
};

} // namespace

char Strip::ID = 0;

bool Strip::runOnModule(Module &M) {
  errs() << "stripping\n";
  LLVMContext *GlobalC = &M.getContext();
  for (auto &F : M) {
    std::string name = demangle(F.getName().str());
    StringRef na(name);
    if (na.startswith("std::") || na.startswith("void std::")) {
        errs() << "remove " << name << "\n";
        errs() << "remove " << F.getName() << "\n";
        SmallVector<BasicBlock *, 8> BBs;
        for (auto &BB : F)
            BBs.push_back(&BB);
        for (auto *BB : BBs) {
            BB->dropAllReferences();
            BB->eraseFromParent();
        }
        BasicBlock *Trampoline = BasicBlock::Create(*GlobalC, "trampoline", &F);
        Type *ORT = F.getReturnType();
        if (!ORT->isVoidTy()) {
            ReturnInst::Create(*GlobalC, Constant::getNullValue(ORT), Trampoline);
        }
        
    }
    //   F.deleteBody();

  }
  return true;
}
INITIALIZE_PASS_BEGIN(Strip, "Strip", "Strip Pass", false, false)
INITIALIZE_PASS_END(Strip, "Strip", "Strip Pass", false, false)

ModulePass *llvm::createStripPass() { return new Strip(); }
