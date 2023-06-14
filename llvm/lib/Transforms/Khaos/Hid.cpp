//===- Hid.cpp ------------------------------------- ---------------===//
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

#define DEBUG_TYPE "Hid"

namespace {
    struct Hid : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        Hid() : ModulePass(ID) {
            initializeHidPass(*PassRegistry::getPassRegistry());
        }
        bool runOnModule(Module &M) override;
    };
}

char Hid::ID = 0;

bool Hid::runOnModule(Module &M) {
    outs() << "control flow hidden pass\n";
    return false;
}

INITIALIZE_PASS_BEGIN(Hid, "Hid", "Hid Pass", false, false)
INITIALIZE_PASS_END(Hid, "Hid", "Hid Pass", false, false)

ModulePass *llvm::createHidPass() {
    return new Hid();
}