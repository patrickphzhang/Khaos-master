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

#include "llvm/ADT/SmallSet.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Khaos/Utils.h"
#include "llvm/Demangle/Demangle.h"
// Khaos
#include "llvm/Transforms/Khaos/Utils.h"

#define DEBUG_TYPE "Hid"

namespace {
    SetVector<CallInst*> CallInLoop;
    SetVector<BranchInst*> BrInLoop;

    struct HidPrepare : public LoopPass {
        static char ID; // Pass identification, replacement for typeid
        HidPrepare() : LoopPass(ID) {
            initializeHidPreparePass(*PassRegistry::getPassRegistry());
        }
        bool runOnLoop(Loop *L, LPPassManager &LPM) override;
        void getAnalysisUsage(AnalysisUsage &AU) const override;
    };
    struct Hid : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        Hid() : ModulePass(ID) {
            initializeHidPass(*PassRegistry::getPassRegistry());
        }
        bool runOnModule(Module &M) override;
        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.setPreservesAll();
            AU.addRequired<LoopInfoWrapperPass>();
            AU.addRequired<DominatorTreeWrapperPass>();
            AU.setPreservesAll();
        }
        
    };


}

char Hid::ID = 0;

bool Hid::runOnModule(Module &M) {
    errs() << "control flow hidden pass\n";
    errs() << "CallInLoop.size(): " << CallInLoop.size() << "\n";
    // return false;
    // M.dump();
    LLVMContext &C = M.getContext();
    bool DiscardValueNames = C.shouldDiscardValueNames();
    C.setDiscardValueNames(false);
    Type *I64 = Type::getInt64Ty(C);
    Type *I64Ptr = Type::getInt64PtrTy(C);
    std::map<Function *, unsigned long long> IndexMap;
    SmallVector<BranchInst *, 8> Brs;
    SmallVector<CallInst *, 8> Calls;
    SmallVector<Constant *, 8> Callees;
    Function *Holder = nullptr;
    unsigned long long Index = 0;
    int count = 0;
    for (auto &F : M) {
        if (F.getName().equals("_Z16khaos_hid_holderv"))
            Holder = &F;
        if (F.skipKhaos()) {
            // errs() << "skipped: " << F.getName() << "\n"; 
            continue;
        }
        if (EnableAutoMode && F.isKhaosFunction())
            continue;
        for (auto &BB : F) {
            for (auto &Inst : BB) {
                if (BranchInst * BI = dyn_cast<BranchInst>(&Inst)) {
                    if (BI->isUnconditional() && !BB.isEHPad() && !BB.isLandingPad() && BrInLoop.count(BI) == 0){
                        Brs.push_back(BI);
                    }
                } /*if (CallInst * CI = dyn_cast<CallInst>(&Inst)) {
                    if (CallInLoop.count(CI))
                        continue;
                    if (Function * Callee = CI->getCalledFunction()) {
                        if (Callee->isIntrinsic() || Callee->isDeclaration() || 
                            Callee->isVarArg() || Callee->hasPersonalityFn() ||
                            Callee->skipKhaos())
                            continue;
                        if(!F.isKhaosFunction()) {
                            Calls.push_back(CI);
                            F.setKhaosFunction(true);
                        }
                    }
                } */
            }
        }
    }
    // hide the calls
    /* errs() << Calls.size() << "calls to hide\n";
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
        if (count > 2000)
            break;
        if(count++ % 20 != 0)
            continue;
        Callee = ToHide->getCalledFunction();
        CalleeIndex = IndexMap[Callee];
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
    }*/
    // return true;
    // hide the jmps
    if (!Holder) {
        errs() << "No holder function, return.\n";
        Brs.clear();
        CallInLoop.clear();
        BrInLoop.clear();
        return false;
    }
    BasicBlock *Throw = &Holder->getEntryBlock(), 
               *LandingPad, *Unreachable;
    for (auto &BB : *Holder)
        if (BB.isLandingPad())
            LandingPad = &BB;
    Unreachable = &Holder->back();
    Throw->setName("throw");
    LandingPad->setName("landingpad");
    Unreachable->setName("unreachable");
    BranchInst *ToTry; 
    Function *Func;
    SmallVector<ReturnInst*, 8> Unused;
    SmallSet<Function *, 8> Copied;
    
    int hidCount = 0;
    while (!Brs.empty()) {
        ToTry = Brs.pop_back_val();

        Func = ToTry->getFunction();
        std::string name = demangle(Func->getName().str());
        if (name.find_first_of("std::") == 0 || name.find_first_of("void std::") == 0)
            continue;
        if (Copied.count(Func) == 1)
            continue;
        BasicBlock *Original = ToTry->getSuccessor(0);
        if (dyn_cast<PHINode>(&(Original->front())))
            continue;
        Copied.insert(Func);
        // hidCount++;
        // if (hidCount > 20 || hidCount <= 19)
        //     continue;1260
        // if (hidCount > 630/* || hidCount <= 646*/)
        //     continue;
        // errs() << "in " << Func->getName() << "\n";
        // errs() << "in " << name << "\n";
        // errs() << "in " << name << "\n";
        // Func->dump();
        Func->setPersonalityFn(Holder->getPersonalityFn());
        ValueToValueMapTy VMap;
        CloneFunctionInto(Func, Holder, VMap, false, Unused, "_khaos", nullptr);
        Throw = LandingPad = Unreachable = nullptr;
        for (auto &BB : *Func) {
            if (BB.getName().equals("throw_khaos"))
                Throw = &BB;
            else if (BB.getName().equals("landingpad_khaos"))
                LandingPad = &BB;
            else if (BB.getName().equals("unreachable_khaos"))
                Unreachable = &BB;
        }
        
        ToTry->setOperand(0, Throw);
        Instruction *Return = LandingPad->getTerminator();
        Return->dropAllReferences();
        Return->eraseFromParent();
        BranchInst::Create(Original, LandingPad);
        for (auto &Phis : Original->phis())
            Phis.replaceIncomingBlockWith(ToTry->getParent(), LandingPad);
        // Func->dump();
        // Func->setKhaosFunction(true);
        break;
    }
    // errs() << "hide jmp count " << hidCount << "\n";
    Holder->deleteBody();
    C.setDiscardValueNames(DiscardValueNames);
    return true;
}

INITIALIZE_PASS_BEGIN(Hid, "Hid", "Hid Pass", false, false)
INITIALIZE_PASS_END(Hid, "Hid", "Hid Pass", false, false)

ModulePass *llvm::createHidPass() {
    return new Hid();
}

char HidPrepare::ID = 0;

void HidPrepare::getAnalysisUsage(AnalysisUsage &AU) const {
    // Legacy analysis pass to compute dominator tree.
    AU.addRequired<DominatorTreeWrapperPass>();
    // Legacy analysis pass to compute loop infomation.  
    AU.addRequired<LoopInfoWrapperPass>();
    // getLoopAnalysisUsage(AU);
    AU.setPreservesAll();
}

bool HidPrepare::runOnLoop(Loop *L, LPPassManager &LPM) {
    // errs() << "HidPrepare::runOnLoop\n";
    for (BasicBlock *BB : L->blocks()) {
        for (Instruction &I : *BB) {
            if (CallInst * CI = dyn_cast<CallInst>(&I)) {
                CallInLoop.insert(CI);
            } else if (BranchInst * Br = dyn_cast<BranchInst>(&I)) {
                if (Br->isUnconditional())
                    BrInLoop.insert(Br);
            }
        }
    }
    return false;
}

INITIALIZE_PASS_BEGIN(HidPrepare, "HidPrepare", "HidPrepare Pass", /*cfgonly=*/true, /*analysis=*/true)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_END(HidPrepare, "HidPrepare", "HidPrepare Pass", /*cfgonly=*/true, /*analysis=*/true)

Pass *llvm::createHidPreparePass() {
  return new HidPrepare();
}
