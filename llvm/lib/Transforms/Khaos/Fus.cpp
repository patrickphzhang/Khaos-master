//===- Fus.cpp ------------------------------------- ---------------===//
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
#include "llvm/IR/Verifier.h"

#define DEBUG_TYPE "Fus"

namespace {
    struct Fus : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        LLVMContext *GlobalC;
        Module *GlobalM;
        Type *GlobalVoid, *GlobalI8, *GlobalI8Ptr, *GlobalI64;
        Function * Fused, * First, * Second;
        SmallVector<Type *, 8> FusedParamTypes, IntTypes, FloatTypes, FirstVectorTypes, SecondVectorTypes;
        DenseMap<Function*, SetVector<Function*> *> CallerCalleeMap;
        Fus() : ModulePass(ID) {
            initializeFusPass(*PassRegistry::getPassRegistry());
        }
        bool runOnModule(Module &M) override;
        BasicBlock *travelBody(Function *start, Function *end, ValueToValueMapTy &V2V);
        void substituteAlias(Function *Dead);
        void substituteCallers(Function *Dead, Function *Live, bool Left);
        void substitutePointers(Function *Dead, Function *Live, bool Left);
        pair<Function *, Function *> pick(SetVector<Function *> &fuseableFunctions);
        void recordParams(Function *F, SmallVector<Type *, 8> &IntTypes, SmallVector<Type *, 8> &FloatTypes,
                          SmallVector<Type *, 8> &VectorTypes, ValueToValueMapTy &V2V);
        void reductParams(SmallVector<Type *, 8> &FusedTypes, SmallVector<Type *, 8> &FirstT, SmallVector<Type *, 8> &SecondT);
        void ffa(Function *F);
        void recordCaller(Function *Dead, std::vector<CallBase *> &Callers);
        void recordPointers(CallBase *CBInst, SetVector<Function *> &FunctionUsers);
        Value *digValue(Value * value);
        void arrangeArgs(Function *Dead, BasicBlock *Trampoline, CallSite CS, SmallVector<Value*, 4> &ArgList, bool Left);
        void patchTrampoline(Function *Dead, Function *Live, bool Left, ValueToValueMapTy &V2V);
        bool isRecursiveCall(Function *left, Function *right);
    };
}

char Fus::ID = 0;

bool Fus::runOnModule(Module &M) {
    GlobalM = &M;
    GlobalC = &M.getContext();
    GlobalI8 = Type::getInt8Ty(*GlobalC);
    GlobalI8Ptr = Type::getInt8PtrTy(*GlobalC);
    GlobalI64 = Type::getInt64Ty(*GlobalC);
    GlobalC->setDiscardValueNames(false);
    SetVector<Function *> IntCandidates;
    SetVector<Function *> FloatCandidates;
    SetVector<Function *> FuncsMayCrossModule;
    SetVector<Function *> SepFuncs;
    for (auto &F : M) {
        if (F.isKhaosFunction()) {
            Function *OriginFunction = M.getFunction(F.getName().substr(0, F.getONL()));
            if (OriginFunction && !SepFuncs.count(OriginFunction))
                SepFuncs.insert(OriginFunction);
        }
        for (auto &BB : F) {
            for (auto &I : BB) {
                if (CallBase *CBInst = dyn_cast<CallBase>(&I)) {
                    Function * CalleeFunc = CBInst->getCalledFunction();
                    if (CalleeFunc && CalleeFunc->isDeclaration())
                        recordPointers(CBInst, FuncsMayCrossModule);
                    Value * CalleeValue = digValue(CBInst->getCalledValue());
                    if (Function * CalleeFunc = dyn_cast<Function>(CalleeValue)) {
                        if (CallerCalleeMap.find(&F) != CallerCalleeMap.end()) {
                            SetVector<Function*> *CalleeSet = CallerCalleeMap[&F];
                            CalleeSet->insert(CalleeFunc);
                        } else {
                            SetVector<Function*> *CalleeSet = new SetVector<Function*>();
                            CalleeSet->insert(CalleeFunc);
                            CallerCalleeMap.insert(make_pair(&F, CalleeSet));
                        }
                    }
                }   
            }
        }
    }
    for (auto &F : M) {
        if (F.isIntrinsic() || F.isDeclaration() || F.isVarArg() || F.mayVarArg() || 
            F.skipKhaos() || F.hasStructArg() || F.getName().find("Fusion") != StringRef::npos)
            continue;
        if (SepOnly && !F.isKhaosFunction())
            continue;
        if (OriOnly && (F.isKhaosFunction() || SepFuncs.count(&F)))
            continue;
        if (FuncsMayCrossModule.count(&F))
            continue;
        if (!F.getReturnType()->isVectorTy() && !F.getReturnType()->isStructTy()) {
            if (F.getReturnType()->isFloatingPointTy()) 
                FloatCandidates.insert(&F);
            else
                IntCandidates.insert(&F);
        }
    }
    
    while (FloatCandidates.size() >= 2 || IntCandidates.size() >= 2) {
        tie(First, Second) = pick(IntCandidates);
        if (First == nullptr || Second == nullptr) {
            tie(First, Second) = pick(FloatCandidates);
            if (First == nullptr || Second == nullptr) 
                continue;
        }
        ValueToValueMapTy V2V;
        FusedParamTypes.clear();
        IntTypes.clear();
        FloatTypes.clear();
        FirstVectorTypes.clear();
        SecondVectorTypes.clear();
        FusedParamTypes.push_back(GlobalI8);
        SmallVector<Type *, 8> FirstIntTypes, leftloatTypes, SecondIntTypes, rightloatTypes;
        recordParams(First, FirstIntTypes, leftloatTypes, FirstVectorTypes, V2V);
        recordParams(Second, SecondIntTypes, rightloatTypes, SecondVectorTypes, V2V);
        reductParams(IntTypes, FirstIntTypes, SecondIntTypes);
        reductParams(FloatTypes, leftloatTypes, rightloatTypes);

        for (uint i = 0; i < IntTypes.size(); i++)
            FusedParamTypes.push_back(IntTypes[i]);
        for (uint i = 0; i < FloatTypes.size(); i++)
            FusedParamTypes.push_back(FloatTypes[i]);
        for (uint i = 0; i < FirstVectorTypes.size(); i++)
            FusedParamTypes.push_back(FirstVectorTypes[i]);
        for (uint i = 0; i < SecondVectorTypes.size(); i++)
            FusedParamTypes.push_back(SecondVectorTypes[i]);
        Type * FusedReturnType;
        if (First->getReturnType()->isVoidTy())
            FusedReturnType = Second->getReturnType();
        else if (Second->getReturnType()->isVoidTy())
            FusedReturnType = First->getReturnType();
        else {
            FusedReturnType = First->getReturnType()->fuse(Second->getReturnType());
            if (!FusedReturnType)
                FusedReturnType = GlobalI64;
        }
        Fused = Function::Create(FunctionType::get(FusedReturnType, FusedParamTypes, false), GlobalValue::InternalLinkage, First->getAddressSpace(),
                                        First->getName() + Second->getName() + "Fusion", GlobalM);
        Fused->setDSOLocal(true);
        BasicBlock *CtrlBB = BasicBlock::Create(*GlobalC, "CtrlBB", Fused);
        ICmpInst *icmp = new ICmpInst(*CtrlBB, ICmpInst::ICMP_EQ, Fused->arg_at(0), ConstantInt::get(GlobalI8, 0));

        Argument *Arg;
        Arg = Fused->arg_at(0);
        V2V[Arg] = Arg;
        Value *Casti;

        for (uint i = 0, indexInt = 1, indexFloat = IntTypes.size() + 1, indexVector = IntTypes.size() + FloatTypes.size() + 1; i < First->arg_size(); i++) {
            Arg = First->arg_at(i);
            if (Arg->getType()->isFloatingPointTy()) {
                if (FusedParamTypes[indexFloat] != Arg->getType())
                    Casti = CastInst::Create(CastInst::getCastOpcode(Fused->arg_at(indexFloat), false, Arg->getType(), false), Fused->arg_at(indexFloat),
                                            Arg->getType(), "", CtrlBB);
                else
                    Casti = Fused->arg_at(indexFloat);
                indexFloat++;
            } else if (Arg->getType()->isVectorTy()) {
                Casti = Fused->arg_at(indexVector);
                indexVector++;
            } else {
                if (FusedParamTypes[indexInt] != Arg->getType())
                    Casti = CastInst::Create(CastInst::getCastOpcode(Fused->arg_at(indexInt), false, Arg->getType(), false), Fused->arg_at(indexInt),
                                            Arg->getType(), "", CtrlBB);
                else
                    Casti = Fused->arg_at(indexInt);
                indexInt++;
            }
            V2V[Arg] = Casti;
        }
        for (uint i = 0, indexInt = 1, indexFloat = IntTypes.size() + 1, indexVector = IntTypes.size() + FloatTypes.size() + FirstVectorTypes.size() + 1; i < Second->arg_size(); i++) {
            Arg = Second->arg_at(i);
            if (Arg->getType()->isFloatingPointTy()) {
                if (FusedParamTypes[indexFloat] != Arg->getType())
                    Casti = CastInst::Create(CastInst::getCastOpcode(Fused->arg_at(indexFloat), false, Arg->getType(), false), Fused->arg_at(indexFloat),
                                            Arg->getType(), "", CtrlBB);
                else
                    Casti = Fused->arg_at(indexFloat);
                indexFloat++;
            } else if (Arg->getType()->isVectorTy()) {
                Casti = Fused->arg_at(indexVector);
                indexVector++;
            } else {
                if (FusedParamTypes[indexInt] != Arg->getType())
                    Casti = CastInst::Create(CastInst::getCastOpcode(Fused->arg_at(indexInt), false, Arg->getType(), false), Fused->arg_at(indexInt),
                                            Arg->getType(), "", CtrlBB);
                else
                    Casti = Fused->arg_at(indexInt);
                indexInt++;
            }
            V2V[Arg] = Casti;
        }
        BasicBlock *FirstHeader = travelBody(First, Fused, V2V);
        BasicBlock *SecondHeader = travelBody(Second, Fused, V2V);
        BranchInst::Create(FirstHeader, SecondHeader, (Value *)icmp, CtrlBB);
        ffa(Fused);
        if (Fused->getAlignment() < 16)
            Fused->setAlignment(16);
        Fused->setCallingConv(min(First->getCallingConv(), Second->getCallingConv()));
        Fused->setKhaosFunction(true);
        Fused->setDSOLocal(true);
        
        if (!SepOnly) {
            substituteAlias(First);
            substituteAlias(Second);
        }
        substituteCallers(First, Fused, true);
        substituteCallers(Second, Fused, false);
        if (!SepOnly) {
            substitutePointers(First, Fused, true);
            substitutePointers(Second, Fused, false);
        }
        First->dropAllReferences();
        Second->dropAllReferences();
        
        if (!SepOnly) {
            patchTrampoline(First, Fused, true, V2V);
            patchTrampoline(Second, Fused, false, V2V);
        } else {
            First->eraseFromParent();
            Second->eraseFromParent();
        }
    }
    if (!SepOnly)
        M.patchIndirectCalls();
    return true;
}

Value *Fus::digValue(Value * value) {
    if (BitCastOperator * BO = dyn_cast<BitCastOperator>(value))
        return digValue(BO->getOperand(0));
    if (GlobalAlias *GA = dyn_cast<GlobalAlias>(value))
        return digValue(GA->getAliasee());
    return value;
}

void Fus::arrangeArgs(Function *Dead, BasicBlock *Trampoline, CallSite CS, SmallVector<Value*, 4> &ArgList, bool Left) {
    SmallVector<Value*, 4> IntArgs, FloatArgs, FirstVectorArgs, SecondVectorArgs, VectorArgs;
    unsigned argIndex = 0, floatI = 0, intI = 0, vectorI1 = 0, vectorI2 = 0;
    Value* Arg;
    Type* ArgT;
    Value *Casti;
    Instruction *I;
    unsigned argSize = 0;
    if (Dead)
        argSize = Dead->arg_size();
    else {
        argSize = CS.arg_size();
        I = CS.getInstruction();
    }
        
    for (argIndex = 0; argIndex < argSize; argIndex++) {
        if (Dead)
            Arg = Dead->arg_at(argIndex);
        else
            Arg = CS.getArgument(argIndex);
        ArgT = Arg->getType();
        if (ArgT->isFloatingPointTy()) {
            if (ArgT != FloatTypes[floatI]) {
                Instruction::CastOps CastOp = CastInst::getCastOpcode(Arg, false, FloatTypes[floatI], false);
                if (Dead)
                    Casti = CastInst::Create(CastOp, Arg, FloatTypes[floatI], "", Trampoline);
                else
                    Casti = CastInst::Create(CastOp, Arg, FloatTypes[floatI], "", I);
                FloatArgs.push_back(Casti);
            } else
                FloatArgs.push_back(Arg);
            floatI++;
        } else if (ArgT->isVectorTy()) {
            if (Left) {
                FirstVectorArgs.push_back(Arg);
                vectorI1++;
            } else {
                SecondVectorArgs.push_back(Arg);
                vectorI2++;
            }
        } else {
            if (ArgT != IntTypes[intI]) {
                Instruction::CastOps CastOp = CastInst::getCastOpcode(Arg, false, IntTypes[intI], false);
                if (Dead)
                    Casti = CastInst::Create(CastOp, Arg, IntTypes[intI], "", Trampoline);
                else
                    Casti = CastInst::Create(CastOp, Arg, IntTypes[intI], "", I);
                IntArgs.push_back(Casti);
            } else
                IntArgs.push_back(Arg);
            intI++;
        }
    }
    for (; intI < IntTypes.size(); intI++)
        IntArgs.push_back(Constant::getNullValue(IntTypes[intI]));
    for (; floatI < FloatTypes.size(); floatI++)
        FloatArgs.push_back(Constant::getNullValue(FloatTypes[floatI]));
    VectorArgs.append(FirstVectorArgs.begin(), FirstVectorArgs.end());
    for (; vectorI1 < FirstVectorTypes.size(); vectorI1++)
        VectorArgs.push_back(Constant::getNullValue(FirstVectorTypes[vectorI1]));
    VectorArgs.append(SecondVectorArgs.begin(), SecondVectorArgs.end());
    for (; vectorI2 < SecondVectorTypes.size(); vectorI2++)
        VectorArgs.push_back(Constant::getNullValue(SecondVectorTypes[vectorI2]));
    if (Left)
        ArgList.push_back(ConstantInt::get(GlobalI8, 0));
    else
        ArgList.push_back(ConstantInt::get(GlobalI8, 1));
    ArgList.append(IntArgs.begin(), IntArgs.end());
    ArgList.append(FloatArgs.begin(), FloatArgs.end());
    ArgList.append(VectorArgs.begin(), VectorArgs.end());
}

void Fus::patchTrampoline(Function *Dead, Function *Live, bool Left, ValueToValueMapTy &V2V) {
    BasicBlock *Trampoline = BasicBlock::Create(*GlobalC, Dead->getName() + "_trampoline", Dead);
    SmallVector<Value*, 4> ArgList;
    CallSite CS;
    arrangeArgs(Dead, Trampoline, CS, ArgList, Left);
    ArrayRef<Value *> NAA(ArgList);
    CallInst *NewCall = CallInst::Create(Live, NAA, "", Trampoline);
    NewCall->setCallingConv(Live->getCallingConv());
    Type *ORT = Dead->getReturnType();
    Value *retVal = nullptr;
    if (!ORT->isVoidTy()) {
        if (ORT != NewCall->getType())
            retVal = CastInst::Create(CastInst::getCastOpcode(NewCall, false, ORT, false), NewCall, ORT, "", Trampoline);
        else
            retVal = NewCall;
    }
    ReturnInst::Create(*GlobalC, retVal, Trampoline);
}

void Fus::recordPointers(CallBase *CBInst, SetVector<Function *> &FunctionUsers) {
    CallSite CS(CBInst);
    for (unsigned argIndex = 0; argIndex < CS.arg_size(); argIndex++) 
        if (Function * func = dyn_cast<Function>(digValue(CS.getArgument(argIndex))))
            FunctionUsers.insert(func);
}

bool Fus::isRecursiveCall(Function *left, Function *right) {
    SetVector<Function*> *CalleeSet1 = CallerCalleeMap[left];
    SetVector<Function*> *CalleeSet2 = CallerCalleeMap[right];
    if ((CalleeSet1 && !CalleeSet1->empty() && CalleeSet1->count(right)) ||
            (CalleeSet2 && !CalleeSet2->empty() && CalleeSet2->count(left)))
        return true;
    return false;
}

pair<Function *, Function *> Fus::pick(SetVector<Function *> &fuseableFunctions) {
    if (!fuseableFunctions.size())
        return make_pair(nullptr, nullptr);
    pair<Function *, Function *> toFuse;
    Function *left = fuseableFunctions.front();
    fuseableFunctions.remove(left);
    unsigned size = fuseableFunctions.size();
    if (!size)
        return make_pair(left, nullptr);
    // unsigned index = rand() % size;
    unsigned index = 0;
    unsigned start = index;
    Function *right = nullptr;
    if (OriOnly) {
        uint leftArgSize = left->int_arg_size();
        if (leftArgSize && leftArgSize < 6) {
            for (uint i = 0; i < fuseableFunctions.size(); i++) {
                right = fuseableFunctions[i];
                if (right->int_arg_size() + leftArgSize < 6) {
                    if (isRecursiveCall(left, right)) {
                        right = nullptr;
                    } else {
                        toFuse = make_pair(left, right);
                        fuseableFunctions.remove(right);
                        return toFuse;
                    }
                }
            }
        }
        if (leftArgSize > 6) {
            for (uint i = 0; i < fuseableFunctions.size(); i++) {
                right = fuseableFunctions[i];
                if (!right->int_arg_size()) {
                    if (isRecursiveCall(left, right)) {
                        right = nullptr;
                    } else {
                        toFuse = make_pair(left, right);
                        fuseableFunctions.remove(right);
                        return toFuse;
                    }
                }
            }
        }
    }
    do {
        right = fuseableFunctions[index];
        StringRef FON = left->getONL() > 0 ? left->getName().substr(0, left->getONL()) : left->getName();
        StringRef SON = right->getONL() > 0 ? right->getName().substr(0, right->getONL()) : right->getName();
        if (FON == SON) {
            right = nullptr;
            index = (index+1) % size;
            continue;
        }
        if (isRecursiveCall(left, right)) {
            right = nullptr;
            index = (index+1) % size;
            continue;
        }
    } while (!right && start != index);
    toFuse = make_pair(left, right);
    fuseableFunctions.remove(right);
    return toFuse;
}

void Fus::recordParams(Function *F, SmallVector<Type *, 8> &IntTypes, SmallVector<Type *, 8> &FloatTypes,
                       SmallVector<Type *, 8> &VectorTypes, ValueToValueMapTy &V2V) {
    Argument *Arg;
    Type * ArgT;
    for (uint i = 0; i < F->arg_size(); i++) {
        Arg = F->arg_at(i);
        if (V2V.count(Arg) != 0)
            continue;
        ArgT = Arg->getType();
        if (ArgT->isFloatingPointTy())
            FloatTypes.push_back(ArgT);
        else if (ArgT->isVectorTy())
            VectorTypes.push_back(ArgT);
        else
            IntTypes.push_back(ArgT);
    }
}

void Fus::reductParams(SmallVector<Type *, 8> &FusedTypes, SmallVector<Type *, 8> &FirstT,
                       SmallVector<Type *, 8> &SecondT) {
    SmallVector<Type *, 8> *Bigger;
    uint CommonLength = 0;
    if (FirstT.size() >= SecondT.size()) {
        Bigger = &FirstT;
        CommonLength = SecondT.size();
    } else {
        Bigger = &SecondT;
        CommonLength = FirstT.size();
    }
    Type * MT;
    uint i = 0;
    for (; i < CommonLength; i++) {
        MT = FirstT[i]->fuse(SecondT[i]);
        if (!MT)
            MT = GlobalI64;
        FusedTypes.push_back(MT);
    }
    for (; i < Bigger->size(); i++)
        FusedTypes.push_back((*Bigger)[i]);
}

BasicBlock *Fus::travelBody(Function *start, Function *end, ValueToValueMapTy &V2V) {
    SmallVector<ReturnInst*, 8> Unused;
    unsigned FSize = end->size();
    CloneFunctionInto(end, start, V2V, true, Unused, "", nullptr);
    BasicBlock *RB = nullptr;
    SmallVector<Instruction *, 4> DyingInsts;
    Type * RT = end->getReturnType();

    if (!RT->isVoidTy()) {
        for (auto &BB : *end) {
            for (auto &I : BB) {
                if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
                    if (Value * RV = RI->getReturnValue()) {
                        Type *ORT = RV->getType();
                        if (ORT != RT) {
                            Value * NRV;
                            if (ORT->isVectorTy() || ORT->isAggregateType()) {
                                AllocaInst *P = new AllocaInst(ORT, GlobalM->getDataLayout().getAllocaAddrSpace(), "", RI);
                                new StoreInst(RV, P, RI);
                                NRV = CastInst::Create(CastInst::getCastOpcode(P, false, RT, false), P, RT, "", RI);
                            } else if (RT->isFloatingPointTy()) {
                                NRV = TruncInst::CreateFPCast(RV, RT, "", RI);
                            } else {
                                NRV = CastInst::Create(CastInst::getCastOpcode(RV, false, RT, false), RV, RT, "", RI);
                            }
                            ReturnInst::Create(*GlobalC, NRV, RI);
                            DyingInsts.push_back(RI);
                        }
                    } else {
                        ReturnInst::Create(*GlobalC, Constant::getNullValue(RT), RI);
                        DyingInsts.push_back(RI);
                    }
                }
            }
        }
        for (auto *I : DyingInsts)
            I->eraseFromParent();
    }
    for (auto FI = end->begin(); FI != end->end(); FI++) {
        if (!FSize) {
            RB = &*FI;
            break;
        }
        else FSize--;
    }
    return RB;
}

void Fus::substituteAlias(Function *Dead) {
    SmallVector<GlobalAlias *, 4> DyingAlias;
    for (auto user : Dead->users()) {
        if (GlobalAlias *GA = dyn_cast<GlobalAlias>(user)) {
            GA->replaceAllUsesWith(Dead);
            DyingAlias.push_back(GA);
        }
    }
    for (auto DeadV : DyingAlias) {
        DeadV->dropAllReferences();
        DeadV->eraseFromParent();
    }
    DyingAlias.clear();
    for (Module::alias_iterator ai = GlobalM->alias_begin(), ae = GlobalM->alias_end(); ai != ae; ai++) {
        GlobalAlias *GA = &*ai;
        Constant *A = GA->getAliasee();
        if (A) {
            if(BitCastOperator * BO = dyn_cast<BitCastOperator>(A)) {
                if(BO->getOperand(0) == Dead) {
                    GA->replaceAllUsesWith(A);
                    DyingAlias.push_back(GA);
                }
            }            
        }
    }
    for (auto DeadV : DyingAlias) {
        DeadV->dropAllReferences();
        DeadV->eraseFromParent();
    }
}

void Fus::substituteCallers(Function *Dead, Function *Live, bool Left) {
    bool DeadRetVoid = Dead->getReturnType()->isVoidTy();
    std::vector<CallBase *> Callers;
    recordCaller(Dead, Callers);
    for (uint i = 0; i < Callers.size(); i++) {
        CallSite CS(Callers.at(i));
        Instruction *I = CS.getInstruction();
        Function *EmptyOld = nullptr;
        BasicBlock *EmptyBB = nullptr;
        SmallVector<Value*, 4> ArgList;
        arrangeArgs(EmptyOld, EmptyBB, CS, ArgList, Left);
        bool HaveUse = !DeadRetVoid && !I->user_empty();
        ArrayRef<Value *> NAA(ArgList);
        Type *ORT = Dead->getReturnType();
        Value * target = nullptr;
        if (isa<CallInst>(I)) {
            CallInst *NewCall = CallInst::Create(Live, NAA, "", I);
            NewCall->setCallingConv(Live->getCallingConv());
            target = NewCall;
            if (HaveUse) {
                if (I->getType() != NewCall->getType()) {
                    if (ORT->isVectorTy() || ORT->isAggregateType())
                        target = new LoadInst(CastInst::CreateBitOrPointerCast(NewCall, ORT->getPointerTo(), "", I), "", I);
                    else
                        target = CastInst::Create(CastInst::getCastOpcode(NewCall, false, I->getType(), false), NewCall, I->getType(), "", I);
                }
                I->replaceAllUsesWith(target);
            }
        } else if (InvokeInst *II = dyn_cast<InvokeInst>(I)) {
            InvokeInst *NI = InvokeInst::Create(Live->getFunctionType(), Live, II->getNormalDest(), II->getUnwindDest(), NAA, "", I);
            NI->setCallingConv(Live->getCallingConv());
            target = NI;
            if (HaveUse) {
                if (I->getType() != NI->getType()) {
                    BasicBlock *RBB = BasicBlock::Create(*GlobalC, "invoke.ret.trampoline.normal", II->getParent()->getParent(), II->getNormalDest());
                    NI->setNormalDest(RBB);
                    BranchInst::Create(II->getNormalDest(), RBB);
                    Instruction *IP = RBB->getFirstNonPHI();
                    if (ORT->isVectorTy() || ORT->isAggregateType())
                        target = new LoadInst(CastInst::CreateBitOrPointerCast(NI, ORT->getPointerTo(), "", IP), "", IP);
                    else
                        target = CastInst::Create(CastInst::getCastOpcode(NI, false, I->getType(), false), NI, I->getType(), "", IP);
                    for (auto &Phis : II->getNormalDest()->phis())
                        Phis.replaceIncomingBlockWith(II->getParent(), RBB);
                }
                I->replaceAllUsesWith(target);
            }
        }
        Value * OC = I->getOperand(0);
        if (CallBase *CI = dyn_cast<CallBase>(I))
            OC = CI->getCalledValue();
        I->eraseFromParent();
        if (OC->use_empty() && !isa<Function>(OC)) {
            if (User * OCAsUser = dyn_cast<User>(OC))
                OCAsUser->dropAllReferences();
            else
                OC->deleteValue();
        }
    }
}

void Fus::recordCaller(Function *Dead, std::vector<CallBase *> &Callers) {
    for (auto &F : *GlobalM) {
        for (auto &BB : F) {
            for (auto &I : BB) {
                if (CallBase *CBInst = dyn_cast<CallBase>(&I)) {
                    Value * CalleeValue = CBInst->getCalledValue();
                    if (isa<Function>(CalleeValue)) {
                        if (CalleeValue == Dead)
                            Callers.push_back(CBInst);
                    } else if (isa<BitCastOperator>(CalleeValue)){
                        Value *CV = digValue(CalleeValue);
                        if (CV == Dead) {
                            Callers.push_back(CBInst);
                        } else if (Function * CalleeFunc = dyn_cast<Function>(CV)) {
                            if (CalleeFunc->isDeclaration() && CalleeFunc->getName() == Dead->getName())
                                Callers.push_back(CBInst);
                        }
                    }
                }
            }
        }
    }
}

void Fus::substitutePointers(Function *Dead, Function *Live, bool Left) {
    if (!Dead->getNumUses())
        return;
    Constant *CA;
    if (Left)
        CA = ConstantInt::get(GlobalI64, 0x8);
    else
        CA = ConstantInt::get(GlobalI64, 0xc);
    Constant *T = ConstantExpr::get(Instruction::Add, ConstantExpr::getPtrToInt(Live, GlobalI64), CA);
    T = ConstantExpr::getIntToPtr(T, GlobalI8Ptr);
    T = ConstantExpr::getPointerCast(T, Dead->getType());
    Dead->replaceAllUsesWith(T);
}

void Fus::ffa(Function *F) {
    AttributeList Fa = F->getAttributes();
    for (const auto &At : Fa.getFnAttributes())
        if (At.isAttributeInSet())
            F->removeFnAttr(At.getKindAsEnum());
    for (const auto &At : Fa.getRetAttributes())
        if (At.isAttributeInSet())
            F->removeAttribute(AttributeList::ReturnIndex, At.getKindAsEnum());
    for (unsigned i = 0; i < F->arg_size(); i++)
        for (const auto &At : Fa.getParamAttributes(i))
            if (At.isAttributeInSet())
                F->removeParamAttr(i, At.getKindAsEnum());
}

INITIALIZE_PASS_BEGIN(Fus, "Fus", "Fus Pass", false, false)
INITIALIZE_PASS_END(Fus, "Fus", "Fus Pass", false, false)

ModulePass *llvm::createFusPass() {
    return new Fus();
}