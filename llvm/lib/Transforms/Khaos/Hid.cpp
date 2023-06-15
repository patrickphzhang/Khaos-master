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

#include "llvm/IR/Instructions.h"
#include "llvm/Support/Casting.h"
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
    // M.dump();
    SmallVector<BranchInst *, 8> Brs;
    SmallVector<CallInst *, 8> Calls;
    for (auto &F : M) {
        // F.dump();
        for (auto &BB : F) {
            for (auto &Inst : BB) {
                if (BranchInst * BI = dyn_cast<BranchInst>(&Inst)) {
                    // BI->dump();
                    Brs.push_back(BI);
                } if (CallInst * CI = dyn_cast<CallInst>(&Inst)) {
                    // BI->dump();
                    Calls.push_back(CI);
                }
            }
        }
    }
    return false;
}

INITIALIZE_PASS_BEGIN(Hid, "Hid", "Hid Pass", false, false)
INITIALIZE_PASS_END(Hid, "Hid", "Hid Pass", false, false)

ModulePass *llvm::createHidPass() {
    return new Hid();
}