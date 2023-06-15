//===- Cat.cpp ------------------------------------- ---------------===//
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

#include "llvm/Transforms/Khaos/Utils.h"

#define DEBUG_TYPE "deobfuscate"

namespace {
    struct CatPass : public ModulePass {
        static char ID; // Pass identification, replacement for typeid

        CatPass() : ModulePass(ID) {}

        bool runOnModule(Module &M) override;

    };

}

char CatPass::ID = 0;

bool CatPass::runOnModule(Module &M) {
	LLVMContext &C = M.getContext();
	Type *VoidTy = Type::getVoidTy(C);
	Function *CatHelper = cast<Function>(M.getOrInsertFunction("deobfuscate_helper", VoidTy).getCallee());
        
	appendToGlobalCtors(M, CatHelper, 0);
	return true;
}

static RegisterPass<CatPass> X("deobfuscate", "Cat Pass");

ModulePass *llvm::createCatPass() {
    return new CatPass();
}

