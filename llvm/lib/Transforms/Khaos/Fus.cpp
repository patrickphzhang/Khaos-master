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
        Function * Fused;
        Function * First;
        Function * Second;
        SmallVector<Type *, 8> FusedParamTypes;
        SmallVector<Type *, 8> IntTypes, FloatTypes, FirstVectorTypes, SecondVectorTypes;
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
                          SmallVector<Type *, 8> &VectorParamTypes, ValueToValueMapTy &V2V);
        void reductParams(SmallVector<Type *, 8> &ParamTypes, SmallVector<Type *, 8> &FirstParamTypes, SmallVector<Type *, 8> &SecondParamTypes);
        void ffa(Function *F);
        void recordCaller(Function *Dead, std::vector<CallBase *> &Callers);
        void recordPointers(CallBase *CB, SetVector<Function *> &UsedFunctions);
        uint getIntArgSize(Function *F);
        Value *getExactValue(Value * value);
        void arrangeArgList(Function *Dead, BasicBlock *TrampolineBB, CallSite CS, SmallVector<Value*, 4> &NewArgs, bool Left);
        void insertTrampolineCall(Function *Dead, Function *Live, bool Left,
                                    ValueToValueMapTy &V2V);
    };
}

char Fus::ID = 0;

Value *Fus::getExactValue(Value * value) {
    if (BitCastOperator * BO = dyn_cast<BitCastOperator>(value))
        return getExactValue(BO->getOperand(0));
    if (GlobalAlias *GA = dyn_cast<GlobalAlias>(value))
        return getExactValue(GA->getAliasee());
    return value;
}

void Fus::arrangeArgList(Function *Dead, BasicBlock *TrampolineBB, CallSite CS, SmallVector<Value*, 4> &NewArgs, bool Left) {
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
            Argi = Dead->getArg(argIdx);
        else
            Argi = CS.getArgument(argIdx);
        ArgiType = Argi->getType();
        if (ArgiType->isFloatingPointTy()) {
            if (ArgiType != FloatTypes[floatIndex]) {
                // add a bit cast to argi
                Instruction::CastOps CastOp = CastInst::getCastOpcode(Argi,
                                                                false, FloatTypes[floatIndex], false);
                if (Dead)
                    BitCasti = CastInst::Create(CastOp, Argi, FloatTypes[floatIndex], "", TrampolineBB);
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
                Instruction::CastOps CastOp = CastInst::getCastOpcode(Argi,
                                                                false, IntTypes[intIndex], false);
                if (Dead)
                    BitCasti = CastInst::Create(CastOp, Argi, IntTypes[intIndex], "", TrampolineBB);
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

void Fus::insertTrampolineCall(Function *Dead, Function *Live, bool Left,
                                                ValueToValueMapTy &V2V) {
    assert(Dead->size() == 0 && "What happened? We have already clean the body of Dead.");
    BasicBlock *TrampolineBB = BasicBlock::Create(*GlobalC, Dead->getName() + "_trampoline", Dead);
    SmallVector<Value*, 4> NewArgs;
    CallSite CS;
    arrangeArgList(Dead, TrampolineBB, CS, NewArgs, Left);
    ArrayRef<Value *> NewArgsArr(NewArgs);
    CallInst *NewCallInst = CallInst::Create(Live, NewArgsArr, "", TrampolineBB);
    NewCallInst->setCallingConv(Live->getCallingConv());
    Type *OldReturnType = Dead->getReturnType();
    Value *retVal = nullptr;
    if (!OldReturnType->isVoidTy()) {
        if (OldReturnType != NewCallInst->getType())
            retVal = CastInst::Create(CastInst::getCastOpcode(NewCallInst, false, OldReturnType, false), NewCallInst, OldReturnType, "", TrampolineBB);
        else
            retVal = NewCallInst;
    }
        
    ReturnInst::Create(*GlobalC, retVal, TrampolineBB);
}

bool Fus::runOnModule(Module &M) {
    GlobalM = &M;
    GlobalC = &M.getContext();
    GlobalI8 = Type::getInt8Ty(*GlobalC);
    GlobalI8Ptr = Type::getInt8PtrTy(*GlobalC);
    GlobalI64 = Type::getInt64Ty(*GlobalC);
    GlobalC->setDiscardValueNames(false);
    // Collect mergeable function.
    SetVector<Function *> IntFuncsToFusion;
    SetVector<Function *> FloatFuncsToFusion;
    SetVector<Function *> FuncsMayPropagate;
    SetVector<Function *> FuncsHasBeenFissioned;
    for (auto &F : M) {
        if (F.isCreatedByKhaos()) {
            StringRef OriginName = F.getName().substr(0, F.getOriginNameLength());
            Function *OriginFunction = M.getFunction(OriginName);
            if (OriginFunction && !FuncsHasBeenFissioned.count(OriginFunction))
                FuncsHasBeenFissioned.insert(OriginFunction);
        }
        for (auto &BB : F) {
            for (auto &Inst : BB) {
                if (CallBase *CB = dyn_cast<CallBase>(&Inst)) {
                    Function * CalleeFunction = CB->getCalledFunction();
                    if (CalleeFunction && CalleeFunction->isDeclaration())
                        recordPointers(CB, FuncsMayPropagate);
                    Value * Callee = getExactValue(CB->getCalledValue());
                    if (Function * CalleeFunction = dyn_cast<Function>(Callee)) {
                        if (CallerCalleeMap.find(&F) != CallerCalleeMap.end()) {
                            SetVector<Function*> *CalleeSet = CallerCalleeMap[&F];
                            CalleeSet->insert(CalleeFunction);
                        } else {
                            SetVector<Function*> *CalleeSet = new SetVector<Function*>();
                            CalleeSet->insert(CalleeFunction);
                            CallerCalleeMap.insert(make_pair(&F, CalleeSet));
                        }
                    }
                }   
            }
        }
    }
    for (auto &F : M) {
        if (F.isIntrinsic() || F.isDeclaration() || F.isVarArg())
            continue;
        if (FissionedFunctionOnly && !F.isCreatedByKhaos())
            continue;
        if (OriginFunctionOnly && (F.isCreatedByKhaos() || FuncsHasBeenFissioned.count(&F)))
            continue;
        if (F.getName() == "main" || F.getName() == "_init" || F.getName().find("Fusion") != StringRef::npos
            || F.getName().find("__cxx_global_var_init") != StringRef::npos
            || F.getName().find("__gxx_personality_v0") != StringRef::npos
            || F.getName().find("__clang_call_terminate") != StringRef::npos
            || F.getName().find("_GLOBAL__sub_I_") != StringRef::npos
            || F.getName().find("extract_ptrval") != StringRef::npos
            || F.getName().find("extract_ctrlbit") != StringRef::npos
            || F.getName().find("extract_ctrlsign") != StringRef::npos
            || F.getName().find("get_random") != StringRef::npos
            || F.getName().contains("INS_6VectorIdEEE5solveIN") // TODO: this is a bug, fix it
            || F.getName().equals("_ZN9EnvirBase15checkTimeLimitsEv")
            || F.getName().startswith("_ZN9TOmnetApp15checkTimeLimitsEv")
            || F.getName().equals("ci_compare")
            || F.getName().startswith("sha_crypt") 
            || F.getName().startswith("OPENSSL_cpuid_setup")
            || F.getName().startswith("wc_lines_avx2") 
            || F.getName().startswith("__warn_memset_zero_len"))
            continue;
        if (FuncsMayPropagate.count(&F))
            continue;
        bool MayVarArg = false;
        for (auto user : F.users()) {
            if (Operator *OperatorUser = dyn_cast<Operator>(user)) {
                Type *TargetType = OperatorUser->getType();
                if (PointerType *TargetPointerType = dyn_cast<PointerType>(TargetType)) {
                    if (FunctionType *TargetFunctionType = dyn_cast<FunctionType>(TargetPointerType->getElementType())) {
                        if (TargetFunctionType->getFunctionNumParams() > F.arg_size()) {
                            MayVarArg = true;
                            break;
                        }
                    }
                }
            }
        }
        if (MayVarArg)
            continue;
        if (!F.getReturnType()->isVectorTy() && !F.getReturnType()->isStructTy()) {
            // errs() << "We do not merge vector type for now\n";
            // errs() << "We do not merge struct type for now\n";
            // In source code, when we use struct/vector as an argument, 
            // it's actually an struct pointer in LLVM IR.
            // The only case the struct/vector arguments exist is in the fissioned functions.
            // We decide not to fusion these functions for two reason:
            // 1. These functions are likely to be inlined in future passes(xxx__eh_resum, see 471 for detail),
            // if we fusion them, it could not be inline any more. That's harmful to the runtime speed.
            // 2. If we handled the struct arguments, we need insert a load at the caller and a load at callee,
            // That may also slow down the runtime speed.
            bool StructArg = false;
            for (auto &Argi : F.args()) {
                if (Argi.getType()->isStructTy()) {
                    StructArg = true;
                    break;
                }
            }
            if (StructArg)
                continue;
            if (F.getReturnType()->isFloatingPointTy()) 
                FloatFuncsToFusion.insert(&F);
            else
                IntFuncsToFusion.insert(&F);
        }
    }
    
    std::map<uint, uint> ArgSizeCount;
    std::map<uint, uint> FusionArgSizeCount;
    while (FloatFuncsToFusion.size() >= 2 || IntFuncsToFusion.size() >= 2) {
        // Random choose two functions to merge.
        tie(First, Second) = pick(IntFuncsToFusion);
        if (First == nullptr || Second == nullptr) {
            tie(First, Second) = pick(FloatFuncsToFusion);
            if (First == nullptr || Second == nullptr) 
                continue;
        }
        if (ArgSizeCount.count(First->arg_size()))
            ArgSizeCount[First->arg_size()]++;
        else
            ArgSizeCount[First->arg_size()] = 1;
        if (ArgSizeCount.count(Second->arg_size()))
            ArgSizeCount[Second->arg_size()]++;
        else
            ArgSizeCount[Second->arg_size()] = 1;
        ValueToValueMapTy V2V;
        FusedParamTypes.clear();
        IntTypes.clear();
        FloatTypes.clear();
        FirstVectorTypes.clear();
        SecondVectorTypes.clear();
        // SmallVector<string, 8> ParamNames;
        // Add the control parameter.
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

        // Construct the Fusion function.
        Type * FusionReturnType;
        if (First->getReturnType()->isVoidTy())
            FusionReturnType = Second->getReturnType();
        else if (Second->getReturnType()->isVoidTy())
            FusionReturnType = First->getReturnType();
        else {
            FusionReturnType = First->getReturnType()->mergeType(Second->getReturnType());
            if (!FusionReturnType)
                FusionReturnType = GlobalI64;
        }
        FunctionType *funcType = FunctionType::get(FusionReturnType, FusedParamTypes, false);
        Fused = Function::Create(funcType, GlobalValue::InternalLinkage, First->getAddressSpace(),
                                        First->getName() + Second->getName() + "Fusion", GlobalM);
        Fused->setDSOLocal(true);
        if (FusionArgSizeCount.count(Fused->arg_size()))
            FusionArgSizeCount[Fused->arg_size()]++;
        else
            FusionArgSizeCount[Fused->arg_size()] = 1;
        // Preparing a condition.
        BasicBlock *CtrlBB = BasicBlock::Create(*GlobalC, "CtrlBB", Fused);
        ICmpInst *icmp = new ICmpInst(*CtrlBB, ICmpInst::ICMP_EQ, Fused->getArg(0), ConstantInt::get(GlobalI8, 0));

        // Build V2V entries for params, First's -> Fusion's
        // Add bitcasts to the args of Fused.
        Argument *Argi;
        // Ctrl bit
        Argi = Fused->getArg(0);
        V2V[Argi] = Argi;
        Value *Casti;

        for (uint i = 0, indexInt = 1, indexFloat = IntTypes.size() + 1, indexVector = IntTypes.size() + FloatTypes.size() + 1; i < First->arg_size(); i++) {
            Argi = First->getArg(i);
            if (Argi->getType()->isFloatingPointTy()) {
                if (FusedParamTypes[indexFloat] != Argi->getType()) {
                    // We meet a float type param, add a cast for float
                    Instruction::CastOps CastOp = CastInst::getCastOpcode(Fused->getArg(indexFloat),
                                                                        false, Argi->getType(), false);
                    Casti = CastInst::Create(CastOp, Fused->getArg(indexFloat),
                                            Argi->getType(), "", CtrlBB);
                } else
                    Casti = Fused->getArg(indexFloat);
                indexFloat++;
            }
            else if (Argi->getType()->isVectorTy()) {
                Casti = Fused->getArg(indexVector);
                indexVector++;
            }
            else {
                if (FusedParamTypes[indexInt] != Argi->getType()){
                    // We meet an int type param, add an entry for int
                    // Since the fusion's param is merged(larger or equal),
                    // we don't need an s/z ext, trunc or bitcast is enough
                    Instruction::CastOps CastOp = CastInst::getCastOpcode(Fused->getArg(indexInt),
                                                                        false, Argi->getType(), false);
                    Casti = CastInst::Create(CastOp, Fused->getArg(indexInt),
                                            Argi->getType(), "", CtrlBB);
                } else {
                    Casti = Fused->getArg(indexInt);
                }
                indexInt++;
            }
            V2V[Argi] = Casti;
        }
        // Build V2V entries for params, Second's -> Fusion's
        for (uint i = 0, indexInt = 1, indexFloat = IntTypes.size() + 1, indexVector = IntTypes.size() + FloatTypes.size() + FirstVectorTypes.size() + 1; i < Second->arg_size(); i++) {
            Argi = Second->getArg(i);
            if (Argi->getType()->isFloatingPointTy()) {
                if (FusedParamTypes[indexFloat] != Argi->getType()) {
                    // We meet a float type param, add an entry for float
                    Instruction::CastOps CastOp = CastInst::getCastOpcode(Fused->getArg(indexFloat),
                                                                        false, Argi->getType(), false);
                    Casti = CastInst::Create(CastOp, Fused->getArg(indexFloat),
                                            Argi->getType(), "", CtrlBB);
                } else {
                    Casti = Fused->getArg(indexFloat);
                }
                indexFloat++;
            }
            else if (Argi->getType()->isVectorTy()) {
                Casti = Fused->getArg(indexVector);
                indexVector++;
            }
            else {
                if (FusedParamTypes[indexInt] != Argi->getType()){
                    // We meet a int type param, add an entry for int
                    Instruction::CastOps CastOp = CastInst::getCastOpcode(Fused->getArg(indexInt),
                                                                        false, Argi->getType(), false);
                    Casti = CastInst::Create(CastOp, Fused->getArg(indexInt),
                                            Argi->getType(), "", CtrlBB);
                } else
                    Casti = Fused->getArg(indexInt);
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
        Fused->setCreatedByKhaos(true);
        Fused->setDSOLocal(true);
        
        if (!FissionedFunctionOnly) {
            substituteAlias(First);
            substituteAlias(Second);
        }
        // Repelace call to First/Second with Fused.
        substituteCallers(First, Fused, true);
        substituteCallers(Second, Fused, false);
        if (!FissionedFunctionOnly) {
            substitutePointers(First, Fused, true);
            substitutePointers(Second, Fused, false);
        }
        // delete the origin body.
        // "deleteBody" will change linkage to external, leading to potential problems
        First->dropAllReferences();
        Second->dropAllReferences();
        
        if (!FissionedFunctionOnly) {
            insertTrampolineCall(First, Fused, true, V2V);
            insertTrampolineCall(Second, Fused, false, V2V);
        } else {
            First->eraseFromParent();
            Second->eraseFromParent();
        }
    }
    if (!FissionedFunctionOnly)
        M.patchIndirectCalls();
    return true;
}

uint Fus::getIntArgSize(Function *F) {
    uint IntArgSize = F->arg_size();
    for (uint i = 0; i < F->arg_size(); i++) {
        Value *Argi = F->getArg(i);
        if (Argi->getType()->isFloatingPointTy())
            IntArgSize--;
    }
    return IntArgSize;
}

void Fus::recordPointers(CallBase *CB, SetVector<Function *> &UsedFunctions) {
    CallSite CS(CB);
    Value* Argi;
    for (unsigned argIdx = 0; argIdx < CS.arg_size(); argIdx++) {
        Argi = getExactValue(CS.getArgument(argIdx));
        if (Function * func = dyn_cast<Function>(Argi))
            UsedFunctions.insert(func);
    }
}

pair<Function *, Function *> Fus::pick(SetVector<Function *> &mergeableFunctions) {
    if (mergeableFunctions.size() == 0)
        return make_pair(nullptr, nullptr);
    pair<Function *, Function *> theTwoToFusion;
    // Whether we can find Second or not, we remove First from the mergeableFunctions anyway.
    Function *theFirst = mergeableFunctions.front();

    mergeableFunctions.remove(theFirst);
    unsigned size = mergeableFunctions.size();
    if (size == 0)
        return make_pair(theFirst, nullptr);
    // unsigned idx = rand() % size;
    unsigned idx = 0;
    unsigned originIdx = idx;
    SetVector<Function*> *CalleeSet1 = CallerCalleeMap[theFirst];
    Function *theSecond = nullptr;
    if (OriginFunctionOnly) {
        // first round, choose the second with arg size restriction
        uint firstArgSize = getIntArgSize(theFirst);
        if (firstArgSize && firstArgSize < 6) {
            for (uint i = 0; i < mergeableFunctions.size(); i++) {
                theSecond = mergeableFunctions[i];
                if (getIntArgSize(theSecond) + firstArgSize < 6) {
                    SetVector<Function*> *CalleeSet2 = CallerCalleeMap[theSecond];
                    if ((CalleeSet1 && !CalleeSet1->empty() && CalleeSet1->count(theSecond)) ||
                            (CalleeSet2 && !CalleeSet2->empty() && CalleeSet2->count(theFirst))) {
                        // errs() << "it's a recusive merge, choose another function.\n";
                        theSecond = nullptr;
                    } else {
                        // we choose this one
                        theTwoToFusion = make_pair(theFirst, theSecond);
                        // Once we remove one element, the size of mergeableFunctions varies too.
                        mergeableFunctions.remove(theSecond);
                        return theTwoToFusion;
                    }
                }
            }
        }
        if (firstArgSize > 6) {
            for (uint i = 0; i < mergeableFunctions.size(); i++) {
                theSecond = mergeableFunctions[i];
                if (getIntArgSize(theSecond) == 0) {
                    SetVector<Function*> *CalleeSet2 = CallerCalleeMap[theSecond];
                    if ((CalleeSet1 && !CalleeSet1->empty() && CalleeSet1->count(theSecond)) ||
                            (CalleeSet2 && !CalleeSet2->empty() && CalleeSet2->count(theFirst))) {
                        // errs() << "it's a recusive merge, choose another function.\n";
                        theSecond = nullptr;
                    } else {
                        // we choose this one
                        theTwoToFusion = make_pair(theFirst, theSecond);
                        // Once we remove one element, the size of mergeableFunctions varies too.
                        mergeableFunctions.remove(theSecond);
                        return theTwoToFusion;
                    }
                }
            }
        }
    }
    // normal path
    do {
        theSecond = mergeableFunctions[idx];
        StringRef FirstOriginName = theFirst->getOriginNameLength() > 0 ? theFirst->getName().substr(0, theFirst->getOriginNameLength()) : theFirst->getName();
        StringRef SecondOriginName = theSecond->getOriginNameLength() > 0 ? theSecond->getName().substr(0, theSecond->getOriginNameLength()) : theSecond->getName();
        if (FirstOriginName == SecondOriginName) {
            // errs() << "these two belong's to one function, choose another function.\n";
            theSecond = nullptr;
            idx = (idx+1) % size;
            continue;
        }
        SetVector<Function*> *CalleeSet2 = CallerCalleeMap[theSecond];
        if ((CalleeSet1 && !CalleeSet1->empty() && CalleeSet1->count(theSecond)) ||
                (CalleeSet2 && !CalleeSet2->empty() && CalleeSet2->count(theFirst))) {
            // errs() << "it's a recusive merge, choose another function.\n";
            theSecond = nullptr;
            idx = (idx+1) % size;
            continue;
        }
        
    } while (!theSecond && originIdx != idx);

    theTwoToFusion = make_pair(theFirst, theSecond);
    // Once we remove one element, the size of mergeableFunctions varies too.
    mergeableFunctions.remove(theSecond);
    return theTwoToFusion;
}

// Collect function's parametter types and names.
void Fus::recordParams(Function *F,
        SmallVector<Type *, 8> &IntTypes,
        SmallVector<Type *, 8> &FloatTypes,
        SmallVector<Type *, 8> &VectorParamTypes,
        ValueToValueMapTy &V2V) {
    Argument *Argi;
    Type * ArgiType;
    for (uint i = 0; i < F->arg_size(); i++) {
        Argi = F->getArg(i);
        if (V2V.count(Argi) != 0)
            continue;
        ArgiType = Argi->getType();
        if (ArgiType->isFloatingPointTy())
            FloatTypes.push_back(ArgiType);
        else if (ArgiType->isVectorTy())
            VectorParamTypes.push_back(ArgiType);
        else
            IntTypes.push_back(ArgiType);
    }
}

void Fus::reductParams(
        SmallVector<Type *, 8> &ParamTypes,
        SmallVector<Type *, 8> &FirstParamTypes,
        SmallVector<Type *, 8> &SecondParamTypes) {
    // we select the small one as the base
    SmallVector<Type *, 8> *Small, *Large;
    if (FirstParamTypes.size() >= SecondParamTypes.size()) {
        Large = &FirstParamTypes;
        Small = &SecondParamTypes;
    } else {
        Large = &SecondParamTypes;
        Small = &FirstParamTypes;
    }
    Type * MergedType;
    uint i = 0;
    for (; i < Small->size(); i++) {
        MergedType = FirstParamTypes[i]->mergeType(SecondParamTypes[i]);
        if (!MergedType)
            MergedType = GlobalI64;
        ParamTypes.push_back(MergedType);
    }
    for (; i < Large->size(); i++)
        ParamTypes.push_back((*Large)[i]);
}

// 1. Replace return with store in start.
// 2. Move basicblocks from start to end.
BasicBlock *Fus::travelBody(Function *start,
                                                Function *end,
                                                ValueToValueMapTy &V2V) {
    const DataLayout &DL = GlobalM->getDataLayout();
    SmallVector<ReturnInst*, 8> Returns;
    ClonedCodeInfo *CodeInfo = nullptr;
    unsigned oldBBNum = end->size();
    CloneFunctionInto(end, start, V2V, true, Returns, "", CodeInfo);
    BasicBlock *retBlock = nullptr;
    // correct return inst
    SmallVector<Instruction *, 4> InstsToKill;
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
                                AllocaInst *Pointer = new AllocaInst(OldReturnType, DL.getAllocaAddrSpace(), "", RI);
                                new StoreInst(RetValue, Pointer, RI);
                                Instruction::CastOps CastOp = CastInst::getCastOpcode(Pointer,
                                                                        false, DestReturnType, false);
                                NewRetValue = CastInst::Create(CastOp, Pointer, DestReturnType, "", RI);
                            } else if (DestReturnType->isFloatingPointTy()) {
                                NewRetValue = TruncInst::CreateFPCast(RetValue, DestReturnType, "", RI);
                            } else {
                                Instruction::CastOps CastOp = CastInst::getCastOpcode(RetValue,
                                                                        false, DestReturnType, false);
                                NewRetValue = CastInst::Create(CastOp, RetValue, DestReturnType, "", RI);
                            }
                            ReturnInst::Create(*GlobalC, NewRetValue, RI);
                            InstsToKill.push_back(RI);
                        }
                    } else {
                        // return void -> return null
                        ReturnInst::Create(*GlobalC, Constant::getNullValue(DestReturnType), RI);
                        InstsToKill.push_back(RI);
                    }
                }
            }
        }
        // Remove origin return.
        for (auto *I : InstsToKill)
            I->eraseFromParent();
    }

    for (auto FI = end->begin(); FI != end->end(); FI++) {
        if (oldBBNum == 0) {
            retBlock = &*FI;
            break;
        }
        else oldBBNum--;
    }

    return retBlock;
}

void Fus::substituteAlias(Function *Dead) {
    // check if Dead's users contain GlobalAlias, if true, replace it with old and delete it.
    SmallVector<GlobalAlias *, 4> GlobalAliasToKill;
    for (auto user : Dead->users()) {
        // direct use
        if (GlobalAlias *GA = dyn_cast<GlobalAlias>(user)) {
            GA->replaceAllUsesWith(Dead);
            GlobalAliasToKill.push_back(GA);
        }
    }
    for (auto toKill : GlobalAliasToKill) {
        toKill->dropAllReferences();
        toKill->eraseFromParent();
    }
    // indirect aliase
    SmallVector<GlobalAlias *, 4> IndirectGlobalAlias;
    GlobalAliasToKill.clear();
    for (Module::alias_iterator ai = GlobalM->alias_begin(), ae = GlobalM->alias_end(); ai != ae; ai++) {
        GlobalAlias *GA = &*ai;
        Constant *aliasee = GA->getAliasee();
        if (aliasee) {
            if(BitCastOperator * BO = dyn_cast<BitCastOperator>(aliasee)) {
                if(BO->getOperand(0) == Dead) {
                    GA->replaceAllUsesWith(aliasee);
                    GlobalAliasToKill.push_back(GA);
                }
            }            
        }
    }
    for (auto toKill : GlobalAliasToKill) {
        toKill->dropAllReferences();
        toKill->eraseFromParent();
    }
}

// Construct arguments for FusionFuction.
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
        arrangeArgList(EmptyOld, EmptyBB, CS, NewArgs, Left);
        bool noUse = oldFuncRetVoid || I->user_empty();
        ArrayRef<Value *> NewArgsArr(NewArgs);
        // Whether the origin callbase is a callinst or an invokeinst,
        // we should replace it with corresponding instruction.
        Type *OldReturnType = Dead->getReturnType();
        Value * target = nullptr;
        if (isa<CallInst>(I)) {
            CallInst *NewCallInst = CallInst::Create(Live, NewArgsArr, "", I);
            NewCallInst->setCallingConv(Live->getCallingConv());
            target = NewCallInst;
            if (!noUse) {
                if (I->getType() != NewCallInst->getType()) {
                    if (OldReturnType->isVectorTy() || OldReturnType->isAggregateType()) {
                        CastInst * ReturnCastInst = CastInst::CreateBitOrPointerCast(NewCallInst, OldReturnType->getPointerTo(), "", I);
                        target = new LoadInst(ReturnCastInst, "", I);
                    } else {
                        Instruction::CastOps CastOp = CastInst::getCastOpcode(NewCallInst,
                                                                        false, I->getType(), false);
                        target = CastInst::Create(CastOp, NewCallInst, I->getType(), "", I);
                    }
                }
                I->replaceAllUsesWith(target);
            }
        } else if (InvokeInst *II = dyn_cast<InvokeInst>(I)) {
            BasicBlock *NormalDest = II->getNormalDest();
            InvokeInst *NewInvoke = InvokeInst::Create(Live->getFunctionType(), Live, NormalDest,
                                II->getUnwindDest(), NewArgsArr, "", I);
            NewInvoke->setCallingConv(Live->getCallingConv());
            target = NewInvoke;
            if (!noUse) {
                if (I->getType() != NewInvoke->getType()) {
                     // We need insert a new normal dest bb for return value bitcast
                    BasicBlock *ReturnBB = BasicBlock::Create(*GlobalC, "invoke.ret.trampoline.normal", II->getParent()->getParent(), NormalDest);
                    NewInvoke->setNormalDest(ReturnBB);
                    BranchInst::Create(NormalDest, ReturnBB);
                    Instruction *InsertPoint = ReturnBB->getFirstNonPHI();
                    if (OldReturnType->isVectorTy() || OldReturnType->isAggregateType()) {
                        CastInst * ReturnCastInst = CastInst::CreateBitOrPointerCast(NewInvoke, OldReturnType->getPointerTo(), "", InsertPoint);
                        target = new LoadInst(ReturnCastInst, "", InsertPoint);
                    } else {
                        Instruction::CastOps CastOp = CastInst::getCastOpcode(NewInvoke,
                                                                        false, I->getType(), false);
                        target = CastInst::Create(CastOp, NewInvoke, I->getType(), "", InsertPoint);
                    }
                    // For all phis in the normal dest, we should change the incoming block to trampoline.
                    for (auto &PI : NormalDest->phis()) {
                            PI.replaceIncomingBlockWith(II->getParent(), ReturnBB);
                    }
                }
                I->replaceAllUsesWith(target);
            }
        } else
            llvm_unreachable("unhandled replace direct call\n");
        assert(I->getNumUses() == 0 && "Dead direct CallInst should not be used any more!");
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
                if (CallBase *CB = dyn_cast<CallBase>(&Inst)) {
                    Value * Callee = CB->getCalledValue();
                    if (isa<Function>(Callee)) {
                        if (Callee == Dead) {
                            Callers.push_back(CB);
                        }
                    } else if (isa<BitCastOperator>(Callee)){
                        Value *CalledValue = getExactValue(Callee);
                        if (CalledValue == Dead) {
                            Callers.push_back(CB);
                        } else if (Function * CalleeFunction = dyn_cast<Function>(CalledValue)) {
                            if (CalleeFunction->isDeclaration() && CalleeFunction->getName() == Dead->getName()) {
                                Callers.push_back(CB);
                            }
                        }
                    }
                }
            }
        }
    }
}

void Fus::substitutePointers(Function *Dead, Function *Live, bool Left) {
    // check if there exist users of old function
    if (Dead->getNumUses() == 0)
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
