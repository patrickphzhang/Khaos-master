//===- FisPosition.cpp ------------------------------------- ---------------===//
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

#define DEBUG_TYPE "position"

namespace {
    struct FisPositionPass : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        const int NumPerGroup = 5;
        FisPositionPass() : ModulePass(ID) {}
        bool runOnModule(Module &M) override;
        void moveBefore(Function *F_src, Function *F_dest);
        void moveAfter(Function *F_src, Function *F_dest);
        void swap(unsigned int src, unsigned int dest, vector<Function*> &v);
    };
}

char FisPositionPass::ID = 0;

bool FisPositionPass::runOnModule(Module &M) {
    vector<Function*> vFunc;
    for (auto ib = M.begin(), ie = M.end(); ib != ie; ib++) {
        Function *tempF = &(*ib);
        if (tempF->isDeclaration() || tempF->isIntrinsic()) continue;
        if (!tempF->isAbsoluteSymbolRef() && !tempF->isExternalLinkage && EnableFus)
            tempF->setName("");
        vFunc.push_back(tempF);
    }
    for (unsigned int i = 0; i < vFunc.size(); i++) {
        unsigned int j = (rand() % (vFunc.size() - i)) % NumPerGroup + i;
        swap(i, j, vFunc);
    }
	return true;
}

void FisPositionPass::moveBefore(Function *F_src, Function *F_dest) {
    F_dest->getParent()->getFunctionList().splice(
        F_dest->getIterator(), F_src->getParent()->getFunctionList(), F_src->getIterator()
    );
}

void FisPositionPass::moveAfter(Function *F_src, Function *F_dest) {
    F_dest->getParent()->getFunctionList().splice(
        ++F_dest->getIterator(), F_src->getParent()->getFunctionList(), F_src->getIterator()
    );
}

void FisPositionPass::swap(unsigned int src, unsigned int dest, vector<Function*> &v) {
    if (src == dest) return;
    Function* F_src = v[src];
    Function* F_dest = v[dest];
    Function* F_dest_sub_1 = v[dest - 1];
    v[src] = F_dest;
    v[dest] = F_src;
    moveBefore(F_dest, F_src);
    moveAfter(F_src, F_dest_sub_1);
}

static RegisterPass<FisPositionPass> X("fis", "FisPosition Pass");

ModulePass *llvm::createFisPositionPass() {
    return new FisPositionPass();
}

