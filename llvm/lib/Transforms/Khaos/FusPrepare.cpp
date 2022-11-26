//===- FusPrepare.cpp - Extract each loop into a new function ----------===//
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


#include "llvm/Transforms/Khaos/Utils.h"

#define DEBUG_TYPE "prepare"

namespace llvm {
    DenseMap<Function*, SetVector<Function*> *> LoopCalleeMap;
}

namespace {
    struct FusPrepare : public FunctionPass {
        static char ID; // Pass identification, replacement for typeid
        FusPrepare() : FunctionPass(ID){}

        bool runOnFunction(Function &F) override;
    };
    
}

char FusPrepare::ID = 0;

bool FusPrepare::runOnFunction(Function &F) {
    for (auto &BB : F) {
        for (auto &Inst : BB) {
            if (CallBase *CB = dyn_cast<CallBase>(&Inst)) {  
                Value * Callee = getExactValue(CB->getCalledValue());
                if (Function * CalleeFunction = dyn_cast<Function>(Callee)) {
                    if (LoopCalleeMap.find(&F) != LoopCalleeMap.end()) {
                        SetVector<Function*> *CalleeSet = LoopCalleeMap[&F];
                        CalleeSet->insert(CalleeFunction);
                    } else {
                        SetVector<Function*> *CalleeSet = new SetVector<Function*>();
                        CalleeSet->insert(CalleeFunction);
                        LoopCalleeMap.insert(make_pair(&F, CalleeSet));
                    }
                }
            }
        }
    }
    return false;
}

static RegisterPass<FusPrepare> X("FusPrepare", "FusPrepare Pass");

Pass *llvm::createFusPreparePass() { return new FusPrepare(); }