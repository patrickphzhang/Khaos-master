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
#include "llvm/IR/Constant.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Khaos/Utils.h"
#include "llvm/Demangle/Demangle.h"

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
    bool DiscardValueNames = C.shouldDiscardValueNames();
    C.setDiscardValueNames(false);
    Type *I64 = Type::getInt64Ty(C);
    Type *I64Ptr = Type::getInt64PtrTy(C);
    std::map<Function *, unsigned long long> IndexMap;
    SmallVector<BranchInst *, 8> Brs;
    SmallVector<CallInst *, 8> Calls;
    SmallVector<Constant *, 8> Callees;
    Function *Holder;
    unsigned long long Index = 0;
    for (auto &F : M) {
        if (F.getName().equals("_Z16khaos_hid_holderv"))
            Holder = &F;
        if (F.skipKhaos()) {
            // errs() << "skipped: " << F.getName() << "\n"; 
            continue;
        }
            
        for (auto &BB : F) {
            for (auto &Inst : BB) {
                if (BranchInst * BI = dyn_cast<BranchInst>(&Inst)) {
                    if (BI->isUnconditional() && !BI->getParent()->isEHPad() && !BI->getParent()->isLandingPad())
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
    // hide the jmps
    if (!Holder) {
        errs() << "No holder function, return.\n";
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
    }
    errs() << "hide count " << hidCount << "\n";
    Holder->deleteBody();
    C.setDiscardValueNames(DiscardValueNames);
    return true;
}

INITIALIZE_PASS_BEGIN(Hid, "Hid", "Hid Pass", false, false)
INITIALIZE_PASS_END(Hid, "Hid", "Hid Pass", false, false)

ModulePass *llvm::createHidPass() {
    return new Hid();
}