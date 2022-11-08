//===- InterFunctionPrepare.cpp - Extract each loop into a new function ----------===//
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

#define DEBUG_TYPE "prepare"

namespace llvm {
    DenseMap<Function*, SetVector<Function*> *> LoopCalleeMap;
}

namespace {
    struct InterFunctionPrepare : public FunctionPass {
        static char ID; // Pass identification, replacement for typeid
        const int DeepLevel = LevelDeepFusion;
        InterFunctionPrepare() : FunctionPass(ID){}

        bool runOnFunction(Function &F) override;
        Value *getExactValue(Value * value);
    };
    
}

char InterFunctionPrepare::ID = 0;

Value *InterFunctionPrepare::getExactValue(Value * value) {
    if (BitCastOperator * BO = dyn_cast<BitCastOperator>(value)) {
        return getExactValue(BO->getOperand(0));
    } else if (GlobalAlias *GA = dyn_cast<GlobalAlias>(value)){
        return getExactValue(GA->getAliasee());
    } else {
        return value;
    }
}

bool InterFunctionPrepare::runOnFunction(Function &F) {
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

// bool InterFunctionPrepare::runOnLoop(Loop *L, LPPassManager &LPM) {

//     Function *Parent = L->getHeader()->getParent();

//     for (auto ib = L->block_begin(), ie = L->block_end(); ib != ie; ib++) {
//         for (Instruction &I : **ib) {
//             if (const CallBase *CI = dyn_cast<CallBase>(&I)) {
//                 Function *Callee = CI->getCalledFunction();
//                 if (LoopCalleeMap.find(Parent) != LoopCalleeMap.end()) {
//                     SetVector<Function*> CalleeSet = LoopCalleeMap[Parent];
//                     CalleeSet.insert(Callee);
//                 }
//                 else {
//                     SetVector<Function*> CalleeSet;
//                     CalleeSet.insert(Callee);
//                     LoopCalleeMap.insert(make_pair(Parent, CalleeSet));
//                 }
//             }
//         }
//     }

//     return false;
// }

static RegisterPass<InterFunctionPrepare> X("InterFunctionPrepare", "InterFunctionPrepare Pass");

Pass *llvm::createInterFunctionPreparePass() { return new InterFunctionPrepare(); }