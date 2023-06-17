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

#include "llvm/IR/Constant.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Value.h"
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
    LLVMContext &C = M.getContext();
    Type *I64 = Type::getInt64Ty(C);
    Type *I64Ptr = Type::getInt64PtrTy(C);
    std::map<Function *, unsigned long long> IndexMap;
    SmallVector<BranchInst *, 8> Brs;
    SmallVector<CallInst *, 8> Calls;
    SmallVector<Constant *, 8> Callees;
    unsigned long long Index = 0;
    for (auto &F : M) {
        for (auto &BB : F) {
            for (auto &Inst : BB) {
                if (BranchInst * BI = dyn_cast<BranchInst>(&Inst)) {
                    if (BI->isUnconditional())
                        Brs.push_back(BI);
                } if (CallInst * CI = dyn_cast<CallInst>(&Inst)) {
                    if (Function * Callee = CI->getCalledFunction()) {
                        if (Callee->isIntrinsic() || Callee->isDeclaration() || 
                            Callee->isVarArg() || Callee->hasPersonalityFn() ||
                            Callee->skipKhaos())
                            continue;
                        Calls.push_back(CI);
                    }
                } 
            }
        }
    }
    // hide the jmps
    outs() << Brs.size() << "branches to hide\n";
    // hide the calls
    outs() << Calls.size() << "calls to hide\n";
    CallInst *ToHide;
    Function *Callee;
    for (uint i = 0; i < Calls.size(); i++) {
        ToHide = Calls[i];
        Callee = ToHide->getCalledFunction();
        if (IndexMap.find(Callee) == IndexMap.end()) {
            IndexMap.insert(std::pair<Function *, unsigned long long>(Callee, Index));
            Index++;
            Callees.push_back(ConstantExpr::getPtrToInt(Callee, I64));
        }
    }
    ArrayType *PTy = ArrayType::get(I64,  Callees.size());
    GlobalVariable *Payload = dyn_cast<GlobalVariable>(M.getOrInsertGlobal("payload", PTy));
    Payload->setInitializer(ConstantArray::get(PTy, Callees));
    unsigned long long CalleeIndex = 0;
    Value *CalledValue;
    while (!Calls.empty()) {
        ToHide = Calls.pop_back_val();
        Callee = ToHide->getCalledFunction();
        CalleeIndex = IndexMap[Callee];
        outs() << Callee->getName() << "  " << CalleeIndex << "\n";
        SmallVector<llvm::Value*, 8> Indices;
        Indices.push_back(ConstantInt::get(I64 ,0));
        Indices.push_back(ConstantInt::get(I64 ,CalleeIndex));
        Constant* GEP = ConstantExpr::getGetElementPtr(PTy, Payload, Indices, true);
        LoadInst *LD = new LoadInst(GEP, "", ToHide);
        LD->setAlignment(8);
        CalledValue = CastInst::CreateBitOrPointerCast(LD, I64Ptr, "", ToHide);
        Value *ICalleeFunction = CastInst::CreatePointerCast(CalledValue, 
                                Callee->getFunctionType()->getPointerTo(), 
                                "", ToHide);
        ToHide->setCalledOperand(ICalleeFunction);
    }
    // M.dump();
    return true;
}

INITIALIZE_PASS_BEGIN(Hid, "Hid", "Hid Pass", false, false)
INITIALIZE_PASS_END(Hid, "Hid", "Hid Pass", false, false)

ModulePass *llvm::createHidPass() {
    return new Hid();
}