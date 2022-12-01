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
        pair<Function *, Function *> pick(SetVector<Function *> &mergeableFunctions);
        void recordParams(Function *F, SmallVector<Type *, 8> &IntTypes, SmallVector<Type *, 8> &FloatTypes,
                          SmallVector<Type *, 8> &VectorTypes, ValueToValueMapTy &V2V);
        void reductParams(SmallVector<Type *, 8> &MergedTypes, SmallVector<Type *, 8> &FirstTypes, SmallVector<Type *, 8> &SecondTypes);
        void ffa(Function *F);
        void recordCaller(Function *Dead, std::vector<CallBase *> &Callers);
        void recordPointers(CallBase *CBInst, SetVector<Function *> &UsedFunctions);
        Value *digValue(Value * value);
        void arrangeArgs(Function *Dead, BasicBlock *Trampoline, CallSite CS, SmallVector<Value*, 4> &NewArgs, bool Left);
        void patchTrampoline(Function *Dead, Function *Live, bool Left, ValueToValueMapTy &V2V);
    };
}

char Fus::ID = 0;

Value *Fus::digValue(Value * value) {
    if (BitCastOperator * BO = dyn_cast<BitCastOperator>(value))
        return digValue(BO->getOperand(0));
    if (GlobalAlias *GA = dyn_cast<GlobalAlias>(value))
        return digValue(GA->getAliasee());
    return value;
}

void Fus::arrangeArgs(Function *Dead, BasicBlock *Trampoline, CallSite CS, SmallVector<Value*, 4> &NewArgs, bool Left) {
    // arrange new arg list
    SmallVector<Value*, 4> IntArgs, FloatArgs, FirstVectorArgs, SecondVectorArgs, VectorArgs;
    // 1. old args
    unsigned argIdx = 0, floatIndex = 0, intIndex = 0, vectorIndex1 = 0, vectorIndex2 = 0;
    Value* Argi;
    Type* ArgiType;
    Value *BitCasti;
    Instruction *I;
    unsigned argSize = 0;
    if (Dead)
        argSize = Dead->arg_size();
    else {
        argSize = CS.arg_size();
        I = CS.getInstruction();
    }
        
    for (argIdx = 0; argIdx < argSize; argIdx++) {
        if (Dead)
            Argi = Dead->arg_at(argIdx);
        else
            Argi = CS.getArgument(argIdx);
        ArgiType = Argi->getType();
        if (ArgiType->isFloatingPointTy()) {
            if (ArgiType != FloatTypes[floatIndex]) {
                // add a bit cast to argi
                Instruction::CastOps CastOp = CastInst::getCastOpcode(Argi,
                                                                false, FloatTypes[floatIndex], false);
                if (Dead)
                    BitCasti = CastInst::Create(CastOp, Argi, FloatTypes[floatIndex], "", Trampoline);
                else
                    BitCasti = CastInst::Create(CastOp, Argi, FloatTypes[floatIndex], "", I);
                FloatArgs.push_back(BitCasti);
            } else
                FloatArgs.push_back(Argi);
            floatIndex++;
        } else if (ArgiType->isVectorTy()) {
            if (Left) {
                FirstVectorArgs.push_back(Argi);
                vectorIndex1++;
            }
            else {
                SecondVectorArgs.push_back(Argi);
                vectorIndex2++;
            }
        } else {
            if (ArgiType != IntTypes[intIndex]) {
                // add a bit cast to argi
                Instruction::CastOps CastOp = CastInst::getCastOpcode(Argi, false, IntTypes[intIndex], false);
                if (Dead)
                    BitCasti = CastInst::Create(CastOp, Argi, IntTypes[intIndex], "", Trampoline);
                else
                    BitCasti = CastInst::Create(CastOp, Argi, IntTypes[intIndex], "", I);
                IntArgs.push_back(BitCasti);
            } else
                IntArgs.push_back(Argi);
            intIndex++;
        }
    }
    // 2.null values
    for (; intIndex < IntTypes.size(); intIndex++)
        IntArgs.push_back(Constant::getNullValue(IntTypes[intIndex]));
    for (; floatIndex < FloatTypes.size(); floatIndex++)
        FloatArgs.push_back(Constant::getNullValue(FloatTypes[floatIndex]));
    VectorArgs.append(FirstVectorArgs.begin(), FirstVectorArgs.end());
    for (; vectorIndex1 < FirstVectorTypes.size(); vectorIndex1++)
        VectorArgs.push_back(Constant::getNullValue(FirstVectorTypes[vectorIndex1]));
    VectorArgs.append(SecondVectorArgs.begin(), SecondVectorArgs.end());
    for (; vectorIndex2 < SecondVectorTypes.size(); vectorIndex2++)
        VectorArgs.push_back(Constant::getNullValue(SecondVectorTypes[vectorIndex2]));
    // 3. merge arg list
    // ctrl bit
    if (Left)
        NewArgs.push_back(ConstantInt::get(GlobalI8, 0));
    else
        NewArgs.push_back(ConstantInt::get(GlobalI8, 1));
    NewArgs.append(IntArgs.begin(), IntArgs.end());
    NewArgs.append(FloatArgs.begin(), FloatArgs.end());
    NewArgs.append(VectorArgs.begin(), VectorArgs.end());
}

void Fus::patchTrampoline(Function *Dead, Function *Live, bool Left, ValueToValueMapTy &V2V) {
    BasicBlock *Trampoline = BasicBlock::Create(*GlobalC, Dead->getName() + "_trampoline", Dead);
    SmallVector<Value*, 4> NewArgs;
    CallSite CS;
    arrangeArgs(Dead, Trampoline, CS, NewArgs, Left);
    ArrayRef<Value *> NewArgsArr(NewArgs);
    CallInst *NewCall = CallInst::Create(Live, NewArgsArr, "", Trampoline);
    NewCall->setCallingConv(Live->getCallingConv());
    Type *OldReturnType = Dead->getReturnType();
    Value *retVal = nullptr;
    if (!OldReturnType->isVoidTy()) {
        if (OldReturnType != NewCall->getType())
            retVal = CastInst::Create(CastInst::getCastOpcode(NewCall, false, OldReturnType, false), NewCall, OldReturnType, "", Trampoline);
        else
            retVal = NewCall;
    }
    ReturnInst::Create(*GlobalC, retVal, Trampoline);
}

bool Fus::runOnModule(Module &M) {
    GlobalM = &M;
    GlobalC = &M.getContext();
    GlobalI8 = Type::getInt8Ty(*GlobalC);
    GlobalI8Ptr = Type::getInt8PtrTy(*GlobalC);
    GlobalI64 = Type::getInt64Ty(*GlobalC);
    GlobalC->setDiscardValueNames(false);
    // Collect mergeable function.
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
                    Value * Callee = digValue(CBInst->getCalledValue());
                    if (Function * CalleeFunc = dyn_cast<Function>(Callee)) {
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
        if (F.isIntrinsic() || F.isDeclaration() || F.isVarArg() || F.mayVarArg() || F.skipKhaos() || F.hasStructArg())
            continue;
        if (SepOnly && !F.isKhaosFunction())
            continue;
        if (OriOnly && (F.isKhaosFunction() || SepFuncs.count(&F)))
            continue;
        if (FuncsMayCrossModule.count(&F))
            continue;
        if (!F.getReturnType()->isVectorTy() && !F.getReturnType()->isStructTy())
            if (F.getReturnType()->isFloatingPointTy()) 
                FloatCandidates.insert(&F);
            else
                IntCandidates.insert(&F);
    }
    
    while (FloatCandidates.size() >= 2 || IntCandidates.size() >= 2) {
        // Random choose two functions to merge.
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

        // Get the parameters' type.
        SmallVector<Type *, 8> FirstIntTypes, FirstFloatTypes, SecondIntTypes, SecondFloatTypes;
        recordParams(First, FirstIntTypes, FirstFloatTypes, FirstVectorTypes, V2V);
        recordParams(Second, SecondIntTypes, SecondFloatTypes, SecondVectorTypes, V2V);

        // merge int params and float params, leave vector params alone.
        reductParams(IntTypes, FirstIntTypes, SecondIntTypes);
        reductParams(FloatTypes, FirstFloatTypes, SecondFloatTypes);

        for (uint i = 0; i < IntTypes.size(); i++)
            FusedParamTypes.push_back(IntTypes[i]);
        for (uint i = 0; i < FloatTypes.size(); i++)
            FusedParamTypes.push_back(FloatTypes[i]);
        for (uint i = 0; i < FirstVectorTypes.size(); i++)
            FusedParamTypes.push_back(FirstVectorTypes[i]);
        for (uint i = 0; i < SecondVectorTypes.size(); i++)
            FusedParamTypes.push_back(SecondVectorTypes[i]);

        // Construct the Fused function.
        Type * FusedReturnType;
        if (First->getReturnType()->isVoidTy())
            FusedReturnType = Second->getReturnType();
        else if (Second->getReturnType()->isVoidTy())
            FusedReturnType = First->getReturnType();
        else {
            FusedReturnType = First->getReturnType()->mergeType(Second->getReturnType());
            if (!FusedReturnType)
                FusedReturnType = GlobalI64;
        }
        Fused = Function::Create(FunctionType::get(FusedReturnType, FusedParamTypes, false), GlobalValue::InternalLinkage, First->getAddressSpace(),
                                        First->getName() + Second->getName() + "Fusion", GlobalM);
        Fused->setDSOLocal(true);
        // Preparing a condition.
        BasicBlock *CtrlBB = BasicBlock::Create(*GlobalC, "CtrlBB", Fused);
        ICmpInst *icmp = new ICmpInst(*CtrlBB, ICmpInst::ICMP_EQ, Fused->arg_at(0), ConstantInt::get(GlobalI8, 0));

        // Build V2V entries for params, First's -> Fused's
        // Add bitcasts to the args of Fused.
        Argument *Argi;
        // Ctrl bit
        Argi = Fused->arg_at(0);
        V2V[Argi] = Argi;
        Value *Casti;

        for (uint i = 0, indexInt = 1, indexFloat = IntTypes.size() + 1, indexVector = IntTypes.size() + FloatTypes.size() + 1; i < First->arg_size(); i++) {
            Argi = First->arg_at(i);
            if (Argi->getType()->isFloatingPointTy()) {
                if (FusedParamTypes[indexFloat] != Argi->getType())
                    Casti = CastInst::Create(CastInst::getCastOpcode(Fused->arg_at(indexFloat), false, Argi->getType(), false), Fused->arg_at(indexFloat),
                                            Argi->getType(), "", CtrlBB);
                else
                    Casti = Fused->arg_at(indexFloat);
                indexFloat++;
            } else if (Argi->getType()->isVectorTy()) {
                Casti = Fused->arg_at(indexVector);
                indexVector++;
            } else {
                if (FusedParamTypes[indexInt] != Argi->getType())
                    Casti = CastInst::Create(CastInst::getCastOpcode(Fused->arg_at(indexInt), false, Argi->getType(), false), Fused->arg_at(indexInt),
                                            Argi->getType(), "", CtrlBB);
                else
                    Casti = Fused->arg_at(indexInt);
                indexInt++;
            }
            V2V[Argi] = Casti;
        }
        // Build V2V entries for params, Second's -> Fused's
        for (uint i = 0, indexInt = 1, indexFloat = IntTypes.size() + 1, indexVector = IntTypes.size() + FloatTypes.size() + FirstVectorTypes.size() + 1; i < Second->arg_size(); i++) {
            Argi = Second->arg_at(i);
            if (Argi->getType()->isFloatingPointTy()) {
                if (FusedParamTypes[indexFloat] != Argi->getType())
                    Casti = CastInst::Create(CastInst::getCastOpcode(Fused->arg_at(indexFloat), false, Argi->getType(), false), Fused->arg_at(indexFloat),
                                            Argi->getType(), "", CtrlBB);
                else
                    Casti = Fused->arg_at(indexFloat);
                indexFloat++;
            } else if (Argi->getType()->isVectorTy()) {
                Casti = Fused->arg_at(indexVector);
                indexVector++;
            } else {
                if (FusedParamTypes[indexInt] != Argi->getType())
                    Casti = CastInst::Create(CastInst::getCastOpcode(Fused->arg_at(indexInt), false, Argi->getType(), false), Fused->arg_at(indexInt),
                                            Argi->getType(), "", CtrlBB);
                else
                    Casti = Fused->arg_at(indexInt);
                indexInt++;
            }
            V2V[Argi] = Casti;
        }
        // Move function body from First/Second to Fused
        BasicBlock *FirstHeader = travelBody(First, Fused, V2V);
        BasicBlock *SecondHeader = travelBody(Second, Fused, V2V);
        BranchInst::Create(FirstHeader, SecondHeader, (Value *)icmp, CtrlBB);
        
        // Fix attributes for Fused, because there are some conflicts between First and Second.
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
        // Repelace call to First/Second with Fused.
        substituteCallers(First, Fused, true);
        substituteCallers(Second, Fused, false);
        if (!SepOnly) {
            substitutePointers(First, Fused, true);
            substitutePointers(Second, Fused, false);
        }
        // delete the origin body.
        // "deleteBody" will change linkage to external, leading to potential problems
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

void Fus::recordPointers(CallBase *CBInst, SetVector<Function *> &UsedFunctions) {
    CallSite CS(CBInst);
    for (unsigned argIdx = 0; argIdx < CS.arg_size(); argIdx++) 
        if (Function * func = dyn_cast<Function>(digValue(CS.getArgument(argIdx))))
            UsedFunctions.insert(func);
}

pair<Function *, Function *> Fus::pick(SetVector<Function *> &mergeableFunctions) {
    if (!mergeableFunctions.size())
        return make_pair(nullptr, nullptr);
    pair<Function *, Function *> toFuse;
    Function *firstF = mergeableFunctions.front();
    mergeableFunctions.remove(firstF);
    unsigned size = mergeableFunctions.size();
    if (!size)
        return make_pair(firstF, nullptr);
    // unsigned idx = rand() % size;
    unsigned idx = 0;
    unsigned originIdx = idx;
    SetVector<Function*> *CalleeSet1 = CallerCalleeMap[firstF];
    Function *secondF = nullptr;
    if (OriOnly) {
        // first round, choose the second with arg size restriction
        uint firstArgSize = firstF->int_arg_size();
        if (firstArgSize && firstArgSize < 6) {
            for (uint i = 0; i < mergeableFunctions.size(); i++) {
                secondF = mergeableFunctions[i];
                if (secondF->int_arg_size() + firstArgSize < 6) {
                    SetVector<Function*> *CalleeSet2 = CallerCalleeMap[secondF];
                    if ((CalleeSet1 && !CalleeSet1->empty() && CalleeSet1->count(secondF)) ||
                            (CalleeSet2 && !CalleeSet2->empty() && CalleeSet2->count(firstF))) {
                        secondF = nullptr;
                    } else {
                        // we choose this one
                        toFuse = make_pair(firstF, secondF);
                        // Once we remove one element, the size of mergeableFunctions varies too.
                        mergeableFunctions.remove(secondF);
                        return toFuse;
                    }
                }
            }
        }
        if (firstArgSize > 6) {
            for (uint i = 0; i < mergeableFunctions.size(); i++) {
                secondF = mergeableFunctions[i];
                if (!secondF->int_arg_size()) {
                    SetVector<Function*> *CalleeSet2 = CallerCalleeMap[secondF];
                    if ((CalleeSet1 && !CalleeSet1->empty() && CalleeSet1->count(secondF)) ||
                            (CalleeSet2 && !CalleeSet2->empty() && CalleeSet2->count(firstF))) {
                        secondF = nullptr;
                    } else {
                        // we choose this one
                        toFuse = make_pair(firstF, secondF);
                        // Once we remove one element, the size of mergeableFunctions varies too.
                        mergeableFunctions.remove(secondF);
                        return toFuse;
                    }
                }
            }
        }
    }
    // normal path
    do {
        secondF = mergeableFunctions[idx];
        StringRef FirstOriginName = firstF->getONL() > 0 ? firstF->getName().substr(0, firstF->getONL()) : firstF->getName();
        StringRef SecondOriginName = secondF->getONL() > 0 ? secondF->getName().substr(0, secondF->getONL()) : secondF->getName();
        if (FirstOriginName == SecondOriginName) {
            secondF = nullptr;
            idx = (idx+1) % size;
            continue;
        }
        SetVector<Function*> *CalleeSet2 = CallerCalleeMap[secondF];
        if ((CalleeSet1 && !CalleeSet1->empty() && CalleeSet1->count(secondF)) ||
                (CalleeSet2 && !CalleeSet2->empty() && CalleeSet2->count(firstF))) {
            // errs() << "it's a recusive merge, choose another function.\n";
            secondF = nullptr;
            idx = (idx+1) % size;
            continue;
        }
        
    } while (!secondF && originIdx != idx);

    toFuse = make_pair(firstF, secondF);
    // Once we remove one element, the size of mergeableFunctions varies too.
    mergeableFunctions.remove(secondF);
    return toFuse;
}

// Collect function's parametter types and names.
void Fus::recordParams(Function *F, SmallVector<Type *, 8> &IntTypes, SmallVector<Type *, 8> &FloatTypes,
                       SmallVector<Type *, 8> &VectorTypes, ValueToValueMapTy &V2V) {
    Argument *Argi;
    Type * ArgiType;
    for (uint i = 0; i < F->arg_size(); i++) {
        Argi = F->arg_at(i);
        if (V2V.count(Argi) != 0)
            continue;
        ArgiType = Argi->getType();
        if (ArgiType->isFloatingPointTy())
            FloatTypes.push_back(ArgiType);
        else if (ArgiType->isVectorTy())
            VectorTypes.push_back(ArgiType);
        else
            IntTypes.push_back(ArgiType);
    }
}

void Fus::reductParams(
        SmallVector<Type *, 8> &MergedTypes,
        SmallVector<Type *, 8> &FirstTypes,
        SmallVector<Type *, 8> &SecondTypes) {
    // we select the small one as the base
    SmallVector<Type *, 8> *Small, *Large;
    if (FirstTypes.size() >= SecondTypes.size()) {
        Large = &FirstTypes;
        Small = &SecondTypes;
    } else {
        Large = &SecondTypes;
        Small = &FirstTypes;
    }
    Type * MergedType;
    uint i = 0;
    for (; i < Small->size(); i++) {
        MergedType = FirstTypes[i]->mergeType(SecondTypes[i]);
        if (!MergedType)
            MergedType = GlobalI64;
        MergedTypes.push_back(MergedType);
    }
    for (; i < Large->size(); i++)
        MergedTypes.push_back((*Large)[i]);
}

// 1. Replace return with store in start.
// 2. Move basicblocks from start to end.
BasicBlock *Fus::travelBody(Function *start, Function *end, ValueToValueMapTy &V2V) {
    SmallVector<ReturnInst*, 8> Returns;
    unsigned oldBBNum = end->size();
    CloneFunctionInto(end, start, V2V, true, Returns, "", nullptr);
    BasicBlock *retBlock = nullptr;
    // correct return inst
    SmallVector<Instruction *, 4> DyingInsts;
    Type * DestReturnType = end->getReturnType();

    if (!DestReturnType->isVoidTy()) {
        for (BasicBlock &Block : *end) {
            for (Instruction &I : Block) {
                if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
                    if (Value * RetValue = RI->getReturnValue()) {
                        Type *OldReturnType = RetValue->getType();
                        if (OldReturnType != DestReturnType) {
                            // add a bitcast
                            Value * NewRetValue;
                            if (OldReturnType->isVectorTy() || OldReturnType->isAggregateType()) {
                                // we need to create a pointer to than return value
                                AllocaInst *Pointer = new AllocaInst(OldReturnType, GlobalM->getDataLayout().getAllocaAddrSpace(), "", RI);
                                new StoreInst(RetValue, Pointer, RI);
                                NewRetValue = CastInst::Create(CastInst::getCastOpcode(Pointer, false, DestReturnType, false), Pointer, DestReturnType, "", RI);
                            } else if (DestReturnType->isFloatingPointTy()) {
                                NewRetValue = TruncInst::CreateFPCast(RetValue, DestReturnType, "", RI);
                            } else {
                                NewRetValue = CastInst::Create(CastInst::getCastOpcode(RetValue, false, DestReturnType, false), RetValue, DestReturnType, "", RI);
                            }
                            ReturnInst::Create(*GlobalC, NewRetValue, RI);
                            DyingInsts.push_back(RI);
                        }
                    } else {
                        ReturnInst::Create(*GlobalC, Constant::getNullValue(DestReturnType), RI);
                        DyingInsts.push_back(RI);
                    }
                }
            }
        }
        // Remove origin return.
        for (auto *I : DyingInsts)
            I->eraseFromParent();
    }

    for (auto FI = end->begin(); FI != end->end(); FI++) {
        if (!oldBBNum) {
            retBlock = &*FI;
            break;
        }
        else oldBBNum--;
    }

    return retBlock;
}

void Fus::substituteAlias(Function *Dead) {
    // check if Dead's users contain GlobalAlias, if true, replace it with old and delete it.
    SmallVector<GlobalAlias *, 4> DyingAlias;
    for (auto user : Dead->users()) {
        // direct use
        if (GlobalAlias *GA = dyn_cast<GlobalAlias>(user)) {
            GA->replaceAllUsesWith(Dead);
            DyingAlias.push_back(GA);
        }
    }
    for (auto toKill : DyingAlias) {
        toKill->dropAllReferences();
        toKill->eraseFromParent();
    }
    // indirect aliase
    SmallVector<GlobalAlias *, 4> IndirectGlobalAlias;
    DyingAlias.clear();
    for (Module::alias_iterator ai = GlobalM->alias_begin(), ae = GlobalM->alias_end(); ai != ae; ai++) {
        GlobalAlias *GA = &*ai;
        Constant *aliasee = GA->getAliasee();
        if (aliasee) {
            if(BitCastOperator * BO = dyn_cast<BitCastOperator>(aliasee)) {
                if(BO->getOperand(0) == Dead) {
                    GA->replaceAllUsesWith(aliasee);
                    DyingAlias.push_back(GA);
                }
            }            
        }
    }
    for (auto toKill : DyingAlias) {
        toKill->dropAllReferences();
        toKill->eraseFromParent();
    }
}

// Construct arguments for FusedFuction.
void Fus::substituteCallers(Function *Dead, Function *Live, bool Left) {
    bool oldFuncRetVoid = Dead->getReturnType()->isVoidTy();
    std::vector<CallBase *> Callers;
    recordCaller(Dead, Callers);
    for (uint i = 0; i < Callers.size(); i++) {
        CallSite CS(Callers.at(i));
        Instruction *I = CS.getInstruction();
        Function *EmptyOld = nullptr;
        BasicBlock *EmptyBB = nullptr;
        SmallVector<Value*, 4> NewArgs;
        arrangeArgs(EmptyOld, EmptyBB, CS, NewArgs, Left);
        bool noUse = oldFuncRetVoid || I->user_empty();
        ArrayRef<Value *> NewArgsArr(NewArgs);
        Type *OldReturnType = Dead->getReturnType();
        Value * target = nullptr;
        if (isa<CallInst>(I)) {
            CallInst *NewCall = CallInst::Create(Live, NewArgsArr, "", I);
            NewCall->setCallingConv(Live->getCallingConv());
            target = NewCall;
            if (!noUse) {
                if (I->getType() != NewCall->getType()) {
                    if (OldReturnType->isVectorTy() || OldReturnType->isAggregateType())
                        target = new LoadInst(CastInst::CreateBitOrPointerCast(NewCall, OldReturnType->getPointerTo(), "", I), "", I);
                    else
                        target = CastInst::Create(CastInst::getCastOpcode(NewCall, false, I->getType(), false), NewCall, I->getType(), "", I);
                }
                I->replaceAllUsesWith(target);
            }
        } else if (InvokeInst *II = dyn_cast<InvokeInst>(I)) {
            InvokeInst *NewInvoke = InvokeInst::Create(Live->getFunctionType(), Live, II->getNormalDest(), II->getUnwindDest(), NewArgsArr, "", I);
            NewInvoke->setCallingConv(Live->getCallingConv());
            target = NewInvoke;
            if (!noUse) {
                if (I->getType() != NewInvoke->getType()) {
                     // We need insert a new normal dest bb for return value bitcast
                    BasicBlock *ReturnBB = BasicBlock::Create(*GlobalC, "invoke.ret.trampoline.normal", II->getParent()->getParent(), II->getNormalDest());
                    NewInvoke->setNormalDest(ReturnBB);
                    BranchInst::Create(II->getNormalDest(), ReturnBB);
                    Instruction *InsertPoint = ReturnBB->getFirstNonPHI();
                    if (OldReturnType->isVectorTy() || OldReturnType->isAggregateType())
                        target = new LoadInst(CastInst::CreateBitOrPointerCast(NewInvoke, OldReturnType->getPointerTo(), "", InsertPoint), "", InsertPoint);
                    else
                        target = CastInst::Create(CastInst::getCastOpcode(NewInvoke, false, I->getType(), false), NewInvoke, I->getType(), "", InsertPoint);
                    // For all phis in the normal dest, we should change the incoming block to trampoline.
                    for (auto &PI : II->getNormalDest()->phis()) {
                        PI.replaceIncomingBlockWith(II->getParent(), ReturnBB);
                    }
                }
                I->replaceAllUsesWith(target);
            }
        }
        Value * OldCallee = I->getOperand(0);
        if (CallBase *CI = dyn_cast<CallBase>(I))
            OldCallee = CI->getCalledValue();
        I->eraseFromParent();
        if (OldCallee->use_empty() && !isa<Function>(OldCallee)) {
            if (User * OldCalleeAsUser = dyn_cast<User>(OldCallee))
                OldCalleeAsUser->dropAllReferences();
            else
                OldCallee->deleteValue();
        }
    }
}

void Fus::recordCaller(Function *Dead, std::vector<CallBase *> &Callers) {
    for (auto &F : *GlobalM) {
        for (auto &BB : F) {
            for (auto &Inst : BB) {
                if (CallBase *CBInst = dyn_cast<CallBase>(&Inst)) {
                    Value * Callee = CBInst->getCalledValue();
                    if (isa<Function>(Callee)) {
                        if (Callee == Dead)
                            Callers.push_back(CBInst);
                    } else if (isa<BitCastOperator>(Callee)){
                        Value *CalledValue = digValue(Callee);
                        if (CalledValue == Dead) {
                            Callers.push_back(CBInst);
                        } else if (Function * CalleeFunc = dyn_cast<Function>(CalledValue)) {
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
    // check if there exist users of old function
    if (!Dead->getNumUses())
        return;
    Constant *ctrlArg; // use the third and the fourth bits. the first bit is used for virtual, the second is used in exception handling
    if (Left)
        ctrlArg = ConstantInt::get(GlobalI64, 0x8);
    else
        ctrlArg = ConstantInt::get(GlobalI64, 0xc);
    Constant *TagConstant = ConstantExpr::get(Instruction::Add, llvm::ConstantExpr::getPtrToInt(Live, GlobalI64), ctrlArg);

    TagConstant = ConstantExpr::getIntToPtr(TagConstant, GlobalI8Ptr);
    TagConstant = ConstantExpr::getPointerCast(TagConstant, Dead->getType());
    Dead->replaceAllUsesWith(TagConstant);
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

INITIALIZE_PASS_BEGIN(Fus, "Fus",
                      "Fus Pass", false, false)
INITIALIZE_PASS_END(Fus, "Fus",
                    "Fus Pass", false, false)

ModulePass *llvm::createFusPass() {
    return new Fus();
}
