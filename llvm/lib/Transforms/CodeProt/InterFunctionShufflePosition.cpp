//===- InterFunctionShufflePosition.cpp ------------------------------------- ---------------===//
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

#include "llvm/Transforms/CodeProt/Utils.h"

#define DEBUG_TYPE "position"

namespace {
    struct InterFunctionShufflePositionPass : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        const string ProtName = PROTNAME_INTERSHUFFLE;
        const int ProtRatio = RatioInterShuffle;
        const int NumPerGroup = 5;
        InterFunctionShufflePositionPass() : ModulePass(ID) {}

        bool runOnModule(Module &M) override;

        void moveBefore(Function *F_src, Function *F_dest);
        void moveAfter(Function *F_src, Function *F_dest);
        void swap(unsigned int src, unsigned int dest, vector<Function*> &v);
        void shuffle(Module &M, int NumPerGroup);
        
    };

}

char InterFunctionShufflePositionPass::ID = 0;

bool InterFunctionShufflePositionPass::runOnModule(Module &M) {

	LLVM_DEBUG(outs() << "InterFunctionShufflePosition debug!\n");

    // for (auto &F : M) {

    //     bool needProtect = inConfigOrRandom(ProtName, M, F, ProtRatio);
    //     if (needProtect) {
    //         LLVM_DEBUG(outs() << "func checked: " << F.getName() << "\n");
    //     } else {
    //         LLVM_DEBUG(outs() << "func nochecked: " << F.getName() << "\n");
    //     }

    // }

    shuffle(M, NumPerGroup);

	return true;

}

void InterFunctionShufflePositionPass::shuffle(Module &M, int NumPerGroup) {
    vector<Function*> vFunc;
    for (auto ib = M.begin(), ie = M.end(); ib != ie; ib++) {
        Function *tempF = &(*ib);
        if (tempF->isDeclaration() || tempF->isIntrinsic()) continue;
        if (tempF->isAbsoluteSymbolRef() || tempF->isExternalLinkage || !EnableInterFunctionFusion) {
            // this function's name can not be changed
            // lto is needed
        } else {
            // rename this function
            tempF->setName("");
        }
        vFunc.push_back(tempF);
    }
    for (unsigned int i = 0; i < vFunc.size(); i++) {
        unsigned int j = (rand() % (vFunc.size() - i)) % NumPerGroup + i;
        swap(i, j, vFunc);
    }
}

void InterFunctionShufflePositionPass::moveBefore(Function *F_src, Function *F_dest) {
    F_dest->getParent()->getFunctionList().splice(
        F_dest->getIterator(), F_src->getParent()->getFunctionList(), F_src->getIterator()
    );
}

void InterFunctionShufflePositionPass::moveAfter(Function *F_src, Function *F_dest) {
    F_dest->getParent()->getFunctionList().splice(
        ++F_dest->getIterator(), F_src->getParent()->getFunctionList(), F_src->getIterator()
    );
}

void InterFunctionShufflePositionPass::swap(unsigned int src, unsigned int dest, vector<Function*> &v) {
    if (src == dest) return;
    Function* F_src = v[src];
    Function* F_dest = v[dest];
    LLVM_DEBUG(outs() << "swap " << F_src->getName() << " and " << F_dest->getName() << "\n");
    Function* F_dest_sub_1 = v[dest - 1];
    v[src] = F_dest;
    v[dest] = F_src;
    moveBefore(F_dest, F_src);
    moveAfter(F_src, F_dest_sub_1);
}

static RegisterPass<InterFunctionShufflePositionPass> X("intershuffleposition", "InterFunctionShufflePosition Pass");

ModulePass *llvm::createInterFunctionShufflePositionPass() {
    return new InterFunctionShufflePositionPass();
}

