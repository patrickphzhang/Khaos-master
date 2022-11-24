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
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Khaos/HarmnessAnalysis.h"
#include "llvm/Transforms/Khaos/DeepFusionPrepare.h"
#include "llvm/IR/Verifier.h"

#define DEBUG_TYPE "Fus"

namespace {
    struct Fus : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        const string KhaosName = KHAOSNAME_FUS;
        const int DeepLevel = LevelDeepFusion;
        LLVMContext *C;
        Module *MM;
        Type *VoidTy, *Int8Ty, *Int8PtrTy, *Int64Ty;
        Function * FusionFunction;
        Function * F1;
        Function * F2;
        DominatorTree *DT = nullptr;
        SmallVector<Type *, 8> FusionParamTypes;
        SmallVector<Type *, 8> IntParamTypes, FloatParamTypes, F1VectorParamTypes, F2VectorParamTypes;
        uint TrampolineID = 0;
        Fus() : ModulePass(ID) {
            initializeFusPass(*PassRegistry::getPassRegistry());
        }
            
        void getAnalysisUsage(AnalysisUsage &AU) const override {
            
            AU.addRequired<BlockFrequencyInfoWrapperPass>();
                AU.addRequired<HarmnessAnalysis>();
                AU.addRequired<LoopInfoWrapperPass>();
                AU.addRequired<DominatorTreeWrapperPass>();
                AU.setPreservesAll();
        }
        bool runOnModule(Module &M) override;
        BasicBlock *moveFunction(Function *SrcFunction,
                                    Function *DestFunction,
                                    Module *M,
                                    ValueToValueMapTy &VMap);
        void replaceAliasUsers(Function *Old);
        void replaceDirectCallers(Function *Old, Function *New, bool IsFirst);
        void replaceIndirectUsers(Function *Old, Function *New, bool IsFirst);
        pair<Function *, Function *> randomChooseFromSet(SetVector<Function *> &set);
        void collectFunctionParams(Function *F,
                                    SmallVector<Type *, 8> &IntParamTypes,
                                    SmallVector<Type *, 8> &FloatParamTypes,
                                    SmallVector<Type *, 8> &VectorParamTypes,
                                    ValueToValueMapTy &VMap);
        void mergeFunctionParams(SmallVector<Type *, 8> &ParamTypes,
                                 SmallVector<Type *, 8> &F1ParamTypes,
                                 SmallVector<Type *, 8> &F2ParamTypes);
        Type* mergeType(Type *T1, Type *T2);
        Value *getExactValue(Value * value);
        bool isEHRelatedFunction(Function *F);
        void deepFusionLevel1(ValueToValueMapTy &VMap, Function *from, Function *to, bool IsFirst);
        bool deepFusionLevel2(ValueToValueMapTy &VMap);
        BasicBlock* preprocessToMergable(BasicBlock *BB);
        void moveAllocas();
        void getHarmlessBasicBlocks(Function *F, std::vector<BasicBlock *> &HarmlessBB);
        BasicBlock *getOneHarmlessBasicBlock(std::vector<BasicBlock *> &HarmlessBB);
        void getValuesNeedPHI(BasicBlock *Root, std::map<Value*, SetVector<Instruction*>*> &Values);
        void insertOpaquePredict(BasicBlock *from, BasicBlock *to, bool IsFirst);
        void ffa(Function *F);
        void getCallInstBySearch(Function *Old, std::vector<CallBase *> &CallUsers);
        void getFunctionUsed(Instruction *I, SetVector<Function *> &UsedFunctions);
        void extractPtrAndCtrlBitAtICall(Module &M);
        uint getIntArgSize(Function *F);
        void arrangeArgList(Function *Old, BasicBlock *TrampolineBB, CallSite CS, SmallVector<Value*, 4> &NewArgs, bool IsFirst);
        void insertTrampolineCall(Function *Old, Function *New, bool IsFirst,
                                    ValueToValueMapTy &VMap);
    };

}

char Fus::ID = 0;

void Fus::arrangeArgList(Function *Old, BasicBlock *TrampolineBB, CallSite CS, SmallVector<Value*, 4> &NewArgs, bool IsFirst) {
    // arrange new arg list
    SmallVector<Value*, 4> IntArgs, FloatArgs, F1VectorArgs, F2VectorArgs, VectorArgs;
    // 1. old args
    unsigned argIdx = 0, floatIndex = 0, intIndex = 0, vectorIndex1 = 0, vectorIndex2 = 0;
    Value* Argi;
    Type* ArgiType;
    Value *BitCasti;
    Instruction *I;
    unsigned argSize = 0;
    if (Old)
        argSize = Old->arg_size();
    else {
        argSize = CS.arg_size();
        I = CS.getInstruction();
    }
        
    for (argIdx = 0; argIdx < argSize; argIdx++) {
        if (Old)
            Argi = Old->getArg(argIdx);
        else
            Argi = CS.getArgument(argIdx);
        
        ArgiType = Argi->getType();
        if (ArgiType->isFloatingPointTy()) {
            if (ArgiType != FloatParamTypes[floatIndex]) {
                // add a bit cast to argi
                Instruction::CastOps CastOp = CastInst::getCastOpcode(Argi,
                                                                false, FloatParamTypes[floatIndex], false);
                if (Old)
                    BitCasti = CastInst::Create(CastOp, Argi, FloatParamTypes[floatIndex], "", TrampolineBB);
                else
                    BitCasti = CastInst::Create(CastOp, Argi, FloatParamTypes[floatIndex], "", I);
                FloatArgs.push_back(BitCasti);
            } else
                FloatArgs.push_back(Argi);
            floatIndex++;
        } else if (ArgiType->isVectorTy()) {
            if (IsFirst) {
                assert(ArgiType == F1VectorParamTypes[vectorIndex1] && "DirectCaller ArgTy is VectorTy but not equals to origin");
                F1VectorArgs.push_back(Argi);
                vectorIndex1++;
            }
            else {
                assert(ArgiType == F2VectorParamTypes[vectorIndex2] && "DirectCaller ArgTy is VectorTy but not equals to origin");
                F2VectorArgs.push_back(Argi);
                vectorIndex2++;
            }
        } else {
            if (ArgiType != IntParamTypes[intIndex]) {
                // add a bit cast to argi
                Instruction::CastOps CastOp = CastInst::getCastOpcode(Argi,
                                                                false, IntParamTypes[intIndex], false);
                if (Old)
                    BitCasti = CastInst::Create(CastOp, Argi, IntParamTypes[intIndex], "", TrampolineBB);
                else
                    BitCasti = CastInst::Create(CastOp, Argi, IntParamTypes[intIndex], "", I);
                IntArgs.push_back(BitCasti);
            } else
                IntArgs.push_back(Argi);
            intIndex++;
        }
    }
    // 2.null values
    for (; intIndex < IntParamTypes.size(); intIndex++)
        IntArgs.push_back(Constant::getNullValue(IntParamTypes[intIndex]));
    for (; floatIndex < FloatParamTypes.size(); floatIndex++)
        FloatArgs.push_back(Constant::getNullValue(FloatParamTypes[floatIndex]));
    VectorArgs.append(F1VectorArgs.begin(), F1VectorArgs.end());
    for (; vectorIndex1 < F1VectorParamTypes.size(); vectorIndex1++)
        VectorArgs.push_back(Constant::getNullValue(F1VectorParamTypes[vectorIndex1]));
    VectorArgs.append(F2VectorArgs.begin(), F2VectorArgs.end());
    for (; vectorIndex2 < F2VectorParamTypes.size(); vectorIndex2++)
        VectorArgs.push_back(Constant::getNullValue(F2VectorParamTypes[vectorIndex2]));
    // 3. merge arg list
    // ctrl bit
    if (IsFirst)
        NewArgs.push_back(ConstantInt::get(Type::getInt8Ty(*C), 0));
    else
        NewArgs.push_back(ConstantInt::get(Type::getInt8Ty(*C), 1));
    NewArgs.append(IntArgs.begin(), IntArgs.end());
    NewArgs.append(FloatArgs.begin(), FloatArgs.end());
    NewArgs.append(VectorArgs.begin(), VectorArgs.end());
}

void Fus::insertTrampolineCall(Function *Old, Function *New, bool IsFirst,
                                                ValueToValueMapTy &VMap) {
    assert(Old->size() == 0 && "What happened? We have already clean the body of Old.");
    auto &Context = New->getContext();
    Module *M = New->getParent();
    BasicBlock *TrampolineBB = BasicBlock::Create(Context, Old->getName() + "_trampoline", Old);
    SmallVector<Value*, 4> NewArgs;
    CallSite CS;
    arrangeArgList(Old, TrampolineBB, CS, NewArgs, IsFirst);
    ArrayRef<Value *> NewArgsArr(NewArgs);
    CallInst *NewCallInst = CallInst::Create(New, NewArgsArr, "", TrampolineBB);
    NewCallInst->setCallingConv(New->getCallingConv());
    Type *OldReturnType = Old->getReturnType();
    Value *retVal = nullptr;
    if (!OldReturnType->isVoidTy()) {
        if (OldReturnType != NewCallInst->getType()) {
            Instruction::CastOps CastOp = CastInst::getCastOpcode(NewCallInst,
                                                            false, OldReturnType, false);
            retVal = CastInst::Create(CastOp, NewCallInst, OldReturnType, "", TrampolineBB);
        } else
            retVal = NewCallInst;
    }
    ReturnInst::Create(M->getContext(), retVal, TrampolineBB);
}

bool Fus::runOnModule(Module &M) {
    MM = &M;
    C = &M.getContext();
    VoidTy = Type::getVoidTy(*C);
    Int8Ty = Type::getInt8Ty(*C);
    Int8PtrTy = Type::getInt8PtrTy(*C);
    Int64Ty = Type::getInt64Ty(*C);
    C->setDiscardValueNames(false);
    uint TotalCount = 0;
    // Collect mergeable function.
    SetVector<Function *> IntDeepFusionFunctions;
    SetVector<Function *> FloatDeepFusionFunctions;
    SetVector<Function *> IntFuncsToFusion;
    SetVector<Function *> FloatFuncsToFusion;
    SetVector<Function *> FuncsMayPropagate;
    SetVector<Function *> FuncsHasBeenFissioned;
    bool DeepFusionMode = false;
    if (DeepLevel > 1 && !EnableFis) {
        DeepFusionMode = true;
    }
    for (auto &F : *MM) {
        if (F.isCreatedByKhaos()) {
            StringRef OriginName = F.getName().substr(0, F.getOriginNameLength());
            Function *OriginFunction = MM->getFunction(OriginName);
            if (OriginFunction && !FuncsHasBeenFissioned.count(OriginFunction)) {
                FuncsHasBeenFissioned.insert(OriginFunction);
            }
        }
        for (auto &BB : F) {
            for (auto &Inst : BB) {
                if (CallBase *CB = dyn_cast<CallBase>(&Inst)) {
                    Function * Callee = CB->getCalledFunction();
                    if (Callee && Callee->isDeclaration()) {
                        // // errs() << "external function " << Callee->getName() << "\n";
                        getFunctionUsed(CB, FuncsMayPropagate);
                    }
                }
            }
        }
    }
    for (auto &F : M) {
        if (F.isIntrinsic() || F.isDeclaration() || F.isVarArg())
            continue;
        if (FissionedFunctionOnly && !F.isCreatedByKhaos()) {
            continue;
        }
        if (OriginFunctionOnly 
            && (F.isCreatedByKhaos() || FuncsHasBeenFissioned.count(&F))) {
            continue;
        }
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
        TotalCount++;
        if (FuncsMayPropagate.count(&F)) {
            continue;
        }
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
        if (F.getReturnType()->isVectorTy()) {
             // errs() << "We do not merge vector type for now\n";
        } else if (F.getReturnType()->isStructTy()) {
            // errs() << "We do not merge struct type for now\n";
        } else {
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
            if (DeepLevel > 1) {
                // deep fusion
                auto const &HarmnessMap = getAnalysis<HarmnessAnalysis>().getHarmnessMap();
                if (HarmnessMap.count(&F) && HarmnessMap.lookup(&F) <= 1
                    && FunctionsWithLoop.find(&F) == FunctionsWithLoop.end()
                    && !isEHRelatedFunction(&F)) {
                    // found a function that can be deep fusioned
                    if (F.getReturnType()->isFloatingPointTy()) {
                        FloatDeepFusionFunctions.insert(&F);
                    } else {
                        IntDeepFusionFunctions.insert(&F);
                    }
                } else {
                    // no it can't
                    if (F.getReturnType()->isFloatingPointTy()) 
                        FloatFuncsToFusion.insert(&F);
                    else
                        IntFuncsToFusion.insert(&F);
                }
            } else {
                if (F.getReturnType()->isFloatingPointTy()) 
                    FloatFuncsToFusion.insert(&F);
                else
                    IntFuncsToFusion.insert(&F);
            }
        }
    }
    // // errs() << "IntFuncsToFusion: " << IntFuncsToFusion.size() << "\n";
    // // errs() << "FloatFuncsToFusion: " << FloatFuncsToFusion.size() << "\n";
    TrampolineID = 0;
    uint MergeCount = 0;
    std::map<uint, uint> ArgSizeCount;
    std::map<uint, uint> FusionArgSizeCount;
    while (FloatFuncsToFusion.size() >= 2 || IntFuncsToFusion.size() >= 2
           || IntDeepFusionFunctions.size() >= 2 || FloatDeepFusionFunctions.size() >= 2) {
        // Random choose two functions to merge.
        tie(F1, F2) = randomChooseFromSet(IntDeepFusionFunctions);
        if (F2 == nullptr) {
            if (F1 == nullptr) {
                // // errs() << "no mergeable function from IntDeepFusionFunctions\n";
                tie(F1, F2) = randomChooseFromSet(FloatDeepFusionFunctions);
                if (F2 == nullptr) {
                    if (F1 == nullptr) {
                        // // errs() << "no mergeable function from FloatDeepFusionFunctions\n";
                        // since no function can be fusioned deeply, we turn off this switch
                        DeepFusionMode = false;
                        tie(F1, F2) = randomChooseFromSet(IntFuncsToFusion);
                        if (F1 == nullptr || F2 == nullptr) {
                            // // errs() << "no mergeable function from IntFuncsToFusion\n";
                            tie(F1, F2) = randomChooseFromSet(FloatFuncsToFusion);
                            if (F1 == nullptr || F2 == nullptr) {
                                // // errs() << "no mergeable function from FloatFuncsToFusion\n";
                                continue;
                            }
                        }
                    } else {
                        // we do not want throw this function away
                        FloatFuncsToFusion.insert(F1);
                        continue;
                    }
                }
            } else {
                // we do not want throw this function away
                IntFuncsToFusion.insert(F1);
                continue;
            }
        }
        
        MergeCount++;
        // !!! do not delete this output util everything is ok
        // errs() << "merging " << F1->getName() << " and " << F2->getName() << "\n";
        outs() << "STATISTICS: merging " << F1->getName() << " and " << F2->getName() << " arg size1: " << F1->arg_size() << " arg size2: " << F2->arg_size() << "\n";
        if (ArgSizeCount.count(F1->arg_size())) {
            ArgSizeCount[F1->arg_size()]++;
        } else {
            ArgSizeCount[F1->arg_size()] = 1;
        }
        if (ArgSizeCount.count(F2->arg_size())) {
            ArgSizeCount[F2->arg_size()]++;
        } else {
            ArgSizeCount[F2->arg_size()] = 1;
        }
        // F1->dump();
        // F2->dump();
        ValueToValueMapTy VMap;
        FusionParamTypes.clear();
        IntParamTypes.clear();
        FloatParamTypes.clear();
        F1VectorParamTypes.clear();
        F2VectorParamTypes.clear();
        SmallVector<string, 8> ParamNames;
        // Add the control parameter.
        FusionParamTypes.push_back(Int8Ty);
        ParamNames.push_back("fusCtrl");

        // Get the parameters' type.
        SmallVector<Type *, 8> F1IntParamTypes, F1FloatParamTypes,
                               F2IntParamTypes, F2FloatParamTypes;
        collectFunctionParams(F1, F1IntParamTypes, F1FloatParamTypes, F1VectorParamTypes, VMap);
        collectFunctionParams(F2, F2IntParamTypes, F2FloatParamTypes, F2VectorParamTypes, VMap);

        // merge int params and float params, leave vector params alone.
        mergeFunctionParams(IntParamTypes, F1IntParamTypes, F2IntParamTypes);
        mergeFunctionParams(FloatParamTypes, F1FloatParamTypes, F2FloatParamTypes);

        for (uint i = 0; i < IntParamTypes.size(); i++) {
            FusionParamTypes.push_back(IntParamTypes[i]);
            ParamNames.push_back(string("argi_").append(itostr(i)));
        }
        for (uint i = 0; i < FloatParamTypes.size(); i++) {
            FusionParamTypes.push_back(FloatParamTypes[i]);
            ParamNames.push_back(string("argf_").append(itostr(i)));
        }
        for (uint i = 0; i < F1VectorParamTypes.size(); i++) {
            FusionParamTypes.push_back(F1VectorParamTypes[i]);
            ParamNames.push_back(string("argv1_").append(itostr(i)));
        }
        for (uint i = 0; i < F2VectorParamTypes.size(); i++) {
            FusionParamTypes.push_back(F2VectorParamTypes[i]);
            ParamNames.push_back(string("argv2_").append(itostr(i)));
        }

        // Construct the Fusion function.
        Type * FusionReturnType;
        if (F1->getReturnType()->isVoidTy()) {
            FusionReturnType = F2->getReturnType();
        } else if (F2->getReturnType()->isVoidTy()) {
            FusionReturnType = F1->getReturnType();
        } else {
            FusionReturnType = mergeType(F1->getReturnType(), F2->getReturnType());
        }
        FunctionType *funcType = FunctionType::get(FusionReturnType, FusionParamTypes, false);
        FusionFunction = Function::Create(funcType, GlobalValue::InternalLinkage, F1->getAddressSpace(),
                                        F1->getName() + F2->getName() + "Fusion", &M);
        outs() << "STATISTICS: fusion function arg size: " << FusionFunction->arg_size() << "\n";
        FusionFunction->setDSOLocal(true);
        if (FusionArgSizeCount.count(FusionFunction->arg_size())) {
            FusionArgSizeCount[FusionFunction->arg_size()]++;
        } else {
            FusionArgSizeCount[FusionFunction->arg_size()] = 1;
        }
        // Set parameters' names for FusionFunction
        Function::arg_iterator DestI = FusionFunction->arg_begin();
        for (unsigned i = 0; i < FusionFunction->arg_size(); i++, &*DestI++)
            DestI->setName(ParamNames[i]);
        // Preparing a condition.
        BasicBlock *CtrlBB = BasicBlock::Create(*C, "CtrlBB", FusionFunction);
        Value *LHS = FusionFunction->getArg(0);
        Value *RHS = ConstantInt::get(Type::getInt8Ty(*C), 0);
        ICmpInst *icmp = new ICmpInst(*CtrlBB, ICmpInst::ICMP_EQ, LHS, RHS);

        // Build VMap entries for params, F1's -> Fusion's
        // Add bitcasts to the args of FusionFunction.
        Argument *Argi;
        // Ctrl bit
        Argi = FusionFunction->getArg(0);
        VMap[Argi] = Argi;
        Value *Casti;

        for (uint i = 0, indexInt = 1, indexFloat = IntParamTypes.size() + 1, indexVector = IntParamTypes.size() + FloatParamTypes.size() + 1; i < F1->arg_size(); i++) {
            Argi = F1->getArg(i);
            if (Argi->getType()->isFloatingPointTy()) {
                if (FusionParamTypes[indexFloat] != Argi->getType()) {
                    // We meet a float type param, add a cast for float
                    Instruction::CastOps CastOp = CastInst::getCastOpcode(FusionFunction->getArg(indexFloat),
                                                                        false, Argi->getType(), false);
                    Casti = CastInst::Create(CastOp, FusionFunction->getArg(indexFloat),
                                            Argi->getType(), "", CtrlBB);
                } else {
                    Casti = FusionFunction->getArg(indexFloat);
                }
                indexFloat++;
            }
            else if (Argi->getType()->isVectorTy()) {
                assert(FusionParamTypes[indexVector] == Argi->getType() && "FusionParamType is VectorTy but not equals to origin");
                Casti = FusionFunction->getArg(indexVector);
                indexVector++;
            }
            else {
                if (FusionParamTypes[indexInt] != Argi->getType()){
                    // We meet an int type param, add an entry for int
                    // Since the fusion's param is merged(larger or equal),
                    // we don't need an s/z ext, trunc or bitcast is enough
                    Instruction::CastOps CastOp = CastInst::getCastOpcode(FusionFunction->getArg(indexInt),
                                                                        false, Argi->getType(), false);
                    Casti = CastInst::Create(CastOp, FusionFunction->getArg(indexInt),
                                            Argi->getType(), "", CtrlBB);
                } else {
                    Casti = FusionFunction->getArg(indexInt);
                }
                indexInt++;
            }
            VMap[Argi] = Casti;
        }
        // Build VMap entries for params, F2's -> Fusion's
        for (uint i = 0, indexInt = 1, indexFloat = IntParamTypes.size() + 1, indexVector = IntParamTypes.size() + FloatParamTypes.size() + F1VectorParamTypes.size() + 1; i < F2->arg_size(); i++) {
            Argi = F2->getArg(i);
            if (Argi->getType()->isFloatingPointTy()) {
                if (FusionParamTypes[indexFloat] != Argi->getType()) {
                    // We meet a float type param, add an entry for float
                    Instruction::CastOps CastOp = CastInst::getCastOpcode(FusionFunction->getArg(indexFloat),
                                                                        false, Argi->getType(), false);
                    Casti = CastInst::Create(CastOp, FusionFunction->getArg(indexFloat),
                                            Argi->getType(), "", CtrlBB);
                } else {
                    Casti = FusionFunction->getArg(indexFloat);
                }
                indexFloat++;
            }
            else if (Argi->getType()->isVectorTy()) {
                assert(FusionParamTypes[indexVector] == Argi->getType() && "FusionParamType is VectorTy but not equals to origin");
                Casti = FusionFunction->getArg(indexVector);
                indexVector++;
            }
            else {
                if (FusionParamTypes[indexInt] != Argi->getType()){
                    // We meet a int type param, add an entry for int
                    Instruction::CastOps CastOp = CastInst::getCastOpcode(FusionFunction->getArg(indexInt),
                                                                        false, Argi->getType(), false);
                    Casti = CastInst::Create(CastOp, FusionFunction->getArg(indexInt),
                                            Argi->getType(), "", CtrlBB);
                } else {
                    Casti = FusionFunction->getArg(indexInt);
                }
                indexInt++;
            }
            VMap[Argi] = Casti;
        }
        // FusionFunction->dump();
        // Move function body from F1/F2 to FusionFunction
        BasicBlock *F1Header = moveFunction(F1, FusionFunction, &M, VMap);
        BasicBlock *F2Header = moveFunction(F2, FusionFunction, &M, VMap);
        BranchInst::Create(F1Header, F2Header, (Value *)icmp, CtrlBB);
        // Check if we need deep fusion
        if (DeepLevel > 0) {
            // it's a three-step process
            // step 1, level 1 for F1->F2
            deepFusionLevel1(VMap, F1, F2, true);
            // step 2, level 1 for F2->F1
            deepFusionLevel1(VMap, F2, F1, false);
            // step 3, level 2 for F1 and F2
            if (DeepLevel > 1 && DeepFusionMode) {
                // backup
                ValueToValueMapTy BKVMap;
                Function *FusionFunctionBK = CloneFunction(FusionFunction, BKVMap);
                if (deepFusionLevel2(VMap) && !verifyFunction(*FusionFunction)) {
                    // good, at least the allocas is merged
                    // remove bk
                    FusionFunctionBK->dropAllReferences();
                    FusionFunctionBK->eraseFromParent();
                } else {
                    // roll back
                    FusionFunction->replaceAllUsesWith(FusionFunctionBK);
                    FusionFunction->dropAllReferences();
                    FusionFunction->eraseFromParent();
                    FusionFunction = FusionFunctionBK;
                }
            }
        }
        
        // Fix attributes for FusionFunction, because there are some conflicts between F1 and F2.
        ffa(FusionFunction);
        if (FusionFunction->getAlignment() < 16) {
            FusionFunction->setAlignment(16);
        }
        assert(FusionFunction->getAlignment() >= 16 && "We need at least 2 bits\n");
        FusionFunction->setCallingConv(min(F1->getCallingConv(), F2->getCallingConv()));
        FusionFunction->setCreatedByKhaos(true);
        FusionFunction->setDSOLocal(true);
        // errs() << "Fusion successed\n";
        // F1->dump();
        // FusionFunction->dump();
        // M.dump();

        if (!FissionedFunctionOnly) {
            replaceAliasUsers(F1);
            replaceAliasUsers(F2);
        }
        // Repelace call to F1/F2 with FusionFunction.
        replaceDirectCallers(F1, FusionFunction, true);
        replaceDirectCallers(F2, FusionFunction, false);
        if (!FissionedFunctionOnly) {
            replaceIndirectUsers(F1, FusionFunction, true);
            replaceIndirectUsers(F2, FusionFunction, false);
        }
        assert(F1->getNumUses() == 0 && F2->getNumUses() == 0 && "there should not be any uses to old function");

        // delete the origin body.
        // "deleteBody" will change linkage to external, leading to potential problems
        F1->dropAllReferences();
        F2->dropAllReferences();
        
        if (!FissionedFunctionOnly) {
            insertTrampolineCall(F1, FusionFunction, true, VMap);
            insertTrampolineCall(F2, FusionFunction, false, VMap);
        } else {
            F1->eraseFromParent();
            F2->eraseFromParent();
        }
    }
    if (!FissionedFunctionOnly) {
        // extractPtrAndCtrlBitAtICall(M);
        M.patchIndirectCalls();
    }
    
    outs() << "STATISTICS: fusion ended, merged " << MergeCount*2 << " of " << TotalCount << " functions\n";
	// M.dump();
    return true;
}

uint Fus::getIntArgSize(Function *F) {
    uint IntArgSize = F->arg_size();
    for (uint i = 0; i < F->arg_size(); i++) {
        Value *Argi = F->getArg(i);
        if (Argi->getType()->isFloatingPointTy()) {
            IntArgSize--;
        }
    }
    return IntArgSize;
}

void Fus::getFunctionUsed(Instruction *I, SetVector<Function *> &UsedFunctions) {
    if (CallBase *CB = dyn_cast<CallBase>(I)) {
        CallSite CS(CB);
        Value* Argi;
        for (unsigned argIdx = 0; argIdx < CS.arg_size(); argIdx++) {
            Argi = getExactValue(CS.getArgument(argIdx));
            if (Function * func = dyn_cast<Function>(Argi)) {
                UsedFunctions.insert(func);
            }
        }
            
    }
}

pair<Function *, Function *> Fus::randomChooseFromSet(SetVector<Function *> &set) {
    if (set.size() == 0)
        return make_pair(nullptr, nullptr);
    pair<Function *, Function *> theTwoToFusion;
    // Whether we can find F2 or not, we remove F1 from the set anyway.
    Function *theFirst = set.front();

    set.remove(theFirst);
    unsigned size = set.size();
    if (size == 0)
        return make_pair(theFirst, nullptr);
    // unsigned idx = rand() % size;
    unsigned idx = 0;
    unsigned originIdx = idx;
    SetVector<Function*> *CalleeSet1 = LoopCalleeMap[theFirst];
    Function *theSecond = nullptr;
    if (OriginFunctionOnly) {
        // first round, choose the second with arg size restriction
        uint firstArgSize = getIntArgSize(theFirst);
        if (firstArgSize && firstArgSize < 6) {
            for (uint i = 0; i < set.size(); i++) {
                theSecond = set[i];
                if (getIntArgSize(theSecond) + firstArgSize < 6) {
                    SetVector<Function*> *CalleeSet2 = LoopCalleeMap[theSecond];
                    if ((CalleeSet1 && !CalleeSet1->empty() && CalleeSet1->count(theSecond)) ||
                            (CalleeSet2 && !CalleeSet2->empty() && CalleeSet2->count(theFirst))) {
                        // // errs() << "it's a recusive merge, choose another function.\n";
                        theSecond = nullptr;
                    } else {
                        // we choose this one
                        theTwoToFusion = make_pair(theFirst, theSecond);
                        // // errs() << "choose by arg\n";
                        // Once we remove one element, the size of set varies too.
                        set.remove(theSecond);
                        return theTwoToFusion;
                    }
                }
            }
        }
        if (firstArgSize > 6) {
            for (uint i = 0; i < set.size(); i++) {
                theSecond = set[i];
                if (getIntArgSize(theSecond) == 0) {
                    SetVector<Function*> *CalleeSet2 = LoopCalleeMap[theSecond];
                    if ((CalleeSet1 && !CalleeSet1->empty() && CalleeSet1->count(theSecond)) ||
                            (CalleeSet2 && !CalleeSet2->empty() && CalleeSet2->count(theFirst))) {
                        // // errs() << "it's a recusive merge, choose another function.\n";
                        theSecond = nullptr;
                    } else {
                        // we choose this one
                        theTwoToFusion = make_pair(theFirst, theSecond);
                        // // errs() << "choose by arg\n";
                        // Once we remove one element, the size of set varies too.
                        set.remove(theSecond);
                        return theTwoToFusion;
                    }
                }
            }
        }
    }
    // normal path
    do {
        theSecond = set[idx];
        StringRef F1OriginName = theFirst->getOriginNameLength() > 0 ? theFirst->getName().substr(0, theFirst->getOriginNameLength()) : theFirst->getName();
        StringRef F2OriginName = theSecond->getOriginNameLength() > 0 ? theSecond->getName().substr(0, theSecond->getOriginNameLength()) : theSecond->getName();
        if (F1OriginName == F2OriginName) {
            // errs() << "these two belong's to one function, choose another function.\n";
            theSecond = nullptr;
            idx = (idx+1) % size;
            continue;
        }
        SetVector<Function*> *CalleeSet2 = LoopCalleeMap[theSecond];
        if ((CalleeSet1 && !CalleeSet1->empty() && CalleeSet1->count(theSecond)) ||
                (CalleeSet2 && !CalleeSet2->empty() && CalleeSet2->count(theFirst))) {
            // // errs() << "it's a recusive merge, choose another function.\n";
            theSecond = nullptr;
            idx = (idx+1) % size;
            continue;
        }
        
    } while (!theSecond && originIdx != idx);

    theTwoToFusion = make_pair(theFirst, theSecond);
    // Once we remove one element, the size of set varies too.
    set.remove(theSecond);
    return theTwoToFusion;
}

// Collect function's parametter types and names.
void Fus::collectFunctionParams(Function *F,
        SmallVector<Type *, 8> &IntParamTypes,
        SmallVector<Type *, 8> &FloatParamTypes,
        SmallVector<Type *, 8> &VectorParamTypes,
        ValueToValueMapTy &VMap) {
    Argument *Argi;
    Type * ArgiType;
    for (uint i = 0; i < F->arg_size(); i++) {
        Argi = F->getArg(i);
        // Copied from other's code.
        if (VMap.count(Argi) != 0)
            continue;
        ArgiType = Argi->getType();
        if (ArgiType->isFloatingPointTy()) {
            FloatParamTypes.push_back(ArgiType);
        }
        else if (ArgiType->isVectorTy()) {
            VectorParamTypes.push_back(ArgiType);
        }
        else {
            IntParamTypes.push_back(ArgiType);
        }
    }
}

void Fus::mergeFunctionParams(
        SmallVector<Type *, 8> &ParamTypes,
        SmallVector<Type *, 8> &F1ParamTypes,
        SmallVector<Type *, 8> &F2ParamTypes) {
    // we select the small one as the base
    SmallVector<Type *, 8> *Small, *Large;
    if (F1ParamTypes.size() >= F2ParamTypes.size()) {
        Large = &F1ParamTypes;
        Small = &F2ParamTypes;
    } else {
        Large = &F2ParamTypes;
        Small = &F1ParamTypes;
    }
    Type * MergedType;
    uint i = 0;
    for (; i < Small->size(); i++) {
        MergedType = mergeType(F1ParamTypes[i], F2ParamTypes[i]);
        ParamTypes.push_back(MergedType);
    }
    for (; i < Large->size(); i++) {
        ParamTypes.push_back((*Large)[i]);
    }
}

Type * Fus::mergeType(Type * T1, Type * T2) {
    if (T1->isStructTy() || T2->isStructTy()
        || T1->isPointerTy() || T2->isPointerTy()
        || T1->isArrayTy() || T2->isArrayTy()
        || T1->isVectorTy() || T2->isVectorTy())
        return Int64Ty;
    else {
        // get size
        assert(T1->isSized() && T2->isSized() && "unhandled case when merging types");
        if (T1->getScalarSizeInBits() > T2->getScalarSizeInBits()) {
            return T1;
        } else {
            return T2;
        }
    }
}

// 1. Replace return with store in SrcFunction.
// 2. Move basicblocks from SrcFunction to DestFunction.
BasicBlock *Fus::moveFunction(Function *SrcFunction,
                                                Function *DestFunction,
                                                Module *M,
                                                ValueToValueMapTy &VMap) {
    // TODO: Calculate the entry frequency of the new root block to preserve profile info?
    // TODO: Remove @llvm.assume calls that will be moved to the new function from the old functions assumption cache?
    LLVMContext &C = M->getContext();
    const DataLayout &DL = M->getDataLayout();
    SmallVector<ReturnInst*, 8> Returns;
    ClonedCodeInfo *CodeInfo = nullptr;
    unsigned oldBBNum = DestFunction->size();
    CloneFunctionInto(DestFunction, SrcFunction, VMap, true, Returns, "",
                    CodeInfo);
    BasicBlock *retBlock = nullptr;
    // correct return inst
    SmallVector<Instruction *, 4> InstsToKill;
    Type * DestReturnType = DestFunction->getReturnType();

    if (!DestReturnType->isVoidTy()) {
        for (BasicBlock &Block : *DestFunction) {
            for (Instruction &I : Block) {
                if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
                    //outs() << "found a return inst\n";
                    if (Value * RetValue = RI->getReturnValue()) {
                        Type *OldReturnType = RetValue->getType();
                        if (OldReturnType != DestReturnType) {
                            // add a bitcast
                            Value * NewRetValue;
                            if (OldReturnType->isVectorTy() || OldReturnType->isAggregateType()) {
                                // we need to create a pointer to than return value
                                assert("OldReturnType is Aggregate or Vector");
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
                            ReturnInst::Create(C, NewRetValue, RI);
                            InstsToKill.push_back(RI);
                        }
                    } else {
                        // return void -> return null
                        ReturnInst::Create(C, Constant::getNullValue(DestReturnType), RI);
                        InstsToKill.push_back(RI);
                    }
                }
            }
        }
        // Remove origin return.
        for (auto *I : InstsToKill)
            I->eraseFromParent();
    }

    for (auto FI = DestFunction->begin(); FI != DestFunction->end(); FI++) {
        if (oldBBNum == 0) {
            retBlock = &*FI;
            break;
        }
        else oldBBNum--;
    }

    return retBlock;
}

bool Fus::isEHRelatedFunction(Function *F) {
    for (auto &BB : *F) {
        if (BB.isEHPad()) {
            return true;
        }
        for (auto &I : BB) {
            if (isa<InvokeInst>(&I)) {
                return true;
            }
        }
    }
    return false;
}

void Fus::deepFusionLevel1(ValueToValueMapTy &VMap, Function *from, Function *to, bool IsFirst) {
    // we do not handle exception irrelevent function
    if (isEHRelatedFunction(from)) {
        return;
    }
    unsigned idxFrom = rand() % (from->size()/2 + from->size()%2);
    unsigned idxTo = rand() % (to->size());
    auto itFrom = from->begin();
    auto itTo = to->begin();
    while (idxFrom-- > 0)
        itFrom++;
    while (idxTo-- > 0)
        itTo++;
    
    Value *valueFrom = VMap[&*itFrom];
    Value *valueTo = VMap[&*itTo];
    BasicBlock *fromBB = dyn_cast<BasicBlock>(valueFrom);
    BasicBlock *toBB = dyn_cast<BasicBlock>(valueTo);
    if (fromBB && toBB)
        insertOpaquePredict(fromBB, toBB, IsFirst);
}

bool Fus::deepFusionLevel2(ValueToValueMapTy &VMap) {
    // 0. merge all the allocas to the Fusion's entry
    moveAllocas();
    // 1. find a mergable pair of basic blocks from f1 and f2
    std::vector<BasicBlock *> HarmlessBBF1, HarmlessBBF2;
    getHarmlessBasicBlocks(F1, HarmlessBBF1);
    getHarmlessBasicBlocks(F2, HarmlessBBF2);
    
    if (HarmlessBBF1.size() == 0 || HarmlessBBF2.size() == 0) {
        // errs() << "no harmless basic block found, return\n";
        return true;
    }
    outs() << "STATISTICS: HarmlessBB count" << HarmlessBBF1.size() << " " << HarmlessBBF2.size() << "\n";
    BasicBlock *BBF1 = getOneHarmlessBasicBlock(HarmlessBBF1);
    BasicBlock *BBF2 = getOneHarmlessBasicBlock(HarmlessBBF2);
    if (BBF1 == nullptr || BBF2 == nullptr) {
        // errs() << "no suitable harmless basic block found, return\n";
        return true;
    }
    outs() << "STATISTICS: HarmlessBB size" << BBF1->size() << " " << BBF2->size() << "\n";
    // 2. get corresponding pair in fusion
    // level 1 deep fusion would split the bb, which affects the mapping
    // use the last instruction to find the correct bb
    Value *value1 = VMap[&BBF1->front()];
    Value *value2 = VMap[&BBF2->front()];
    Instruction *FirstInst1 = dyn_cast<Instruction>(value1);
    Instruction *FirstInst2 = dyn_cast<Instruction>(value2);
    assert(FirstInst1 && FirstInst2 && "empty map!");
    BasicBlock *BB1 = FirstInst1->getParent();
    BasicBlock *BB2 = FirstInst2->getParent();
    assert(BB1 && BB2 && "Can not find the corresponding bb in fusion function!");
    if (BB1 == &FusionFunction->getEntryBlock() || 
        BB2 == &FusionFunction->getEntryBlock() ||
        BB1 == BB2) {
        // errs() << "We cannot merge entry BB\n";
        return true;
    }
    for (BasicBlock *Pred : predecessors(BB1)) {
        if (Pred == &FusionFunction->getEntryBlock()) {
            for (BasicBlock *Pred2 : predecessors(BB2)) {
                if (Pred2 == &FusionFunction->getEntryBlock()) {
                    // this means we are merging entry BB's successor, which is meaningless
                    return true;
                }
            }
        } 
    }
    // 3. preprocess them, spilit phis and jccs, get the mergable part
    BB1 = preprocessToMergable(BB1);
    BB2 = preprocessToMergable(BB2);
    // After the preprocess, the candidates maybe small.
    // If they are small(like a branch), cancel the merge.
    if (BB1->size() == 1 || BB2->size() == 1) {
        // errs() << "they are too small to merge\n";
        return true;
    }
    // 4. record all the needed phis.
    // this will be used after merge
    std::map<Value*, SetVector<Instruction*>*> ValuesNeedPHIForBB1, ValuesNeedPHIForBB2;
    getValuesNeedPHI(BB1, ValuesNeedPHIForBB1);
    getValuesNeedPHI(BB2, ValuesNeedPHIForBB2);

    // 5. add phis in BB2, these phis are for BB2's instruction
    // phi [null, BB1's pred], [normal_value, BB2's pred]
    // as we have preprocessed BB2, we don't need to consider the original phis
    BasicBlock::iterator It = BB2->begin();
    while (It != BB2->end()) {
        Instruction *Inst = &*It;
        It++;
        if (isa<BranchInst>(Inst)) continue;
        if (PHINode *phi = dyn_cast<PHINode>(Inst)) {
            for (BasicBlock *Pred : predecessors(BB1)) {
                phi->addIncoming(Constant::getNullValue(phi->getType()), Pred); 
            }
            continue;
        }
        uint OperandNum = Inst->getNumOperands();
        Value * Opi;
        for (uint i = 0; i < OperandNum; i++) {
            Opi = Inst->getOperand(i);
            if (isa<Constant>(Opi)) {
                continue;
            } 
            // check if this operand needs a phi
            if (Instruction *OpiInst = dyn_cast<Instruction>(Opi)) {
                BasicBlock *DefBB = OpiInst->getParent();
                if (DefBB == &FusionFunction->getEntryBlock() || DefBB == BB2) {
                    // no need
                    continue;
                }
                PHINode *phi = PHINode::Create(Opi->getType(), 0, "", &BB2->front());
                for (BasicBlock *Pred : predecessors(BB2)) {
                   phi->addIncoming(Opi, Pred); 
                }
                for (BasicBlock *Pred : predecessors(BB1)) {
                   phi->addIncoming(Constant::getNullValue(Opi->getType()), Pred); 
                }
                Inst->replaceUsesOfWith(Opi, phi);
            }
        }
    }
    // FusionFunction->dump();
    // 5. merge them
    uint size = BB1->size();
    Instruction *InsertPos = &*BB2->getFirstInsertionPt();
    while (size > 1) {
        Instruction *ToMove = &BB1->front();
        assert(!isa<PHINode>(ToMove) && "There should't be any PHIs in BB1\n");
        ToMove->moveAfter(InsertPos);
        InsertPos = ToMove;
        // simply move instruction is not enough
        // 6. add phis in BB2, these phis are for BB1's instruction
        // phi [null, BB2's pred], [normal_value, BB1's pred]
        if (PHINode *phi = dyn_cast<PHINode>(ToMove)) {
            for (BasicBlock *Pred : predecessors(BB2)) {
                phi->addIncoming(Constant::getNullValue(phi->getType()), Pred); 
            }
            continue;
        }
        uint OperandNum = ToMove->getNumOperands();
        size--;
        Value * Opi;
        for (uint i = 0; i < OperandNum; i++) {
            Opi = ToMove->getOperand(i);
            if (isa<Constant>(Opi)) {
                continue;
            } 
            // check if this operand needs a phi
            if (Instruction *OpiInst = dyn_cast<Instruction>(Opi)) {
                BasicBlock *DefBB = OpiInst->getParent();
                if (DefBB == &FusionFunction->getEntryBlock() || DefBB == BB2) {
                    // no need
                    continue;
                }
                PHINode *phi = PHINode::Create(Opi->getType(), 0, "", &BB2->front());
                for (BasicBlock *Pred : predecessors(BB1)) {
                   phi->addIncoming(Opi, Pred); 
                }
                for (BasicBlock *Pred : predecessors(BB2)) {
                   phi->addIncoming(Constant::getNullValue(Opi->getType()), Pred); 
                }
                ToMove->replaceUsesOfWith(Opi, phi);
            }
        }
    }
    // 7. add phis in BB2, these phis are needed because we changed the CFG
    for (auto it = ValuesNeedPHIForBB1.begin(), 
              ie = ValuesNeedPHIForBB1.end(); it != ie; it++) {
        Value *ValueNeedPHI = it->first;
        PHINode *phi = PHINode::Create(ValueNeedPHI->getType(), 0, "", &BB2->front());
        for (BasicBlock *Pred : predecessors(BB1)) {
            phi->addIncoming(ValueNeedPHI, Pred); 
        }
        for (BasicBlock *Pred : predecessors(BB2)) {
            phi->addIncoming(Constant::getNullValue(ValueNeedPHI->getType()), Pred); 
        }

        SetVector<Instruction*> *UseInsts = it->second;
        while (UseInsts->size()) {
            Instruction *UseInst = UseInsts->pop_back_val();
            UseInst->replaceUsesOfWith(ValueNeedPHI, phi);
        }
    }
    for (auto it = ValuesNeedPHIForBB2.begin(), 
              ie = ValuesNeedPHIForBB2.end(); it != ie; it++) {
        Value *ValueNeedPHI = it->first;
        SetVector<Instruction*> *UseInsts = it->second;
        PHINode *phi = PHINode::Create(ValueNeedPHI->getType(), 0, "", &BB2->front());
        for (BasicBlock *Pred : predecessors(BB2)) {
            phi->addIncoming(ValueNeedPHI, Pred); 
        }
        for (BasicBlock *Pred : predecessors(BB1)) {
            phi->addIncoming(Constant::getNullValue(ValueNeedPHI->getType()), Pred); 
        }
        while (UseInsts->size()) {
            Instruction *UseInst = UseInsts->pop_back_val();
            UseInst->replaceUsesOfWith(ValueNeedPHI, phi);
        }
    }
    BB1->replaceAllUsesWith(BB2);
    
    BranchInst *BI1 = dyn_cast<BranchInst>(&BB1->back());
    BranchInst *BI2 = dyn_cast<BranchInst>(&BB2->back());
    assert(BI1 && BI1->isUnconditional() && "There should be an unconditional branch!");
    assert(BI2 && BI2->isUnconditional() && "There should be an unconditional branch!");
    BasicBlock *TargetBB1 = dyn_cast<BasicBlock>(BI1->getOperand(0));
    BasicBlock *TargetBB2 = dyn_cast<BasicBlock>(BI2->getOperand(0));
    BI2->eraseFromParent();
    Value *LHS = FusionFunction->getArg(0);
    Value *RHS = ConstantInt::get(Int8Ty, 0);
    ICmpInst *icmp = new ICmpInst(*BB2, ICmpInst::ICMP_EQ, LHS, RHS);
    BranchInst::Create(TargetBB1, TargetBB2, (Value *)icmp, BB2);
    BB1->eraseFromParent();
    if (!verifyFunction(*FusionFunction)) {
        outs() << "STATISTICS: deepFusionLevel2 succeed\n";
        return true;
    } else {
        outs() << "STATISTICS: deepFusionLevel2 failed\n";
        return false;
    }
}

BasicBlock* Fus::preprocessToMergable(BasicBlock *BB) {
    // split the head and tail, get the body part
    // split head
    BasicBlock::iterator i1 = BB->begin();
    if (&*i1 != BB->getFirstNonPHIOrDbgOrLifetime()) {
        i1 = (BasicBlock::iterator)BB->getFirstNonPHIOrDbgOrLifetime();
        BB = BB->splitBasicBlock(i1);
    }
    // split tail
    i1 = --(BB->end());
    if (BranchInst *bi = dyn_cast<BranchInst>(&*i1)) {
        if (bi->isConditional()) {
            // assumption: cmp and branch are neighbor
            // --i1;
            // assert(isa<CmpInst>(&*i1) && "We assume cmp and branch are neighbors!");
            BB->splitBasicBlock(i1);
        }
    }
    // We may optimize this later, adding bitcasts or phis instead of spiliting.
    i1 = --(BB->end());
    if (ReturnInst *bi = dyn_cast<ReturnInst>(&*i1)) {
        BB->splitBasicBlock(i1);
    }
    return BB;
}

BasicBlock* Fus::getOneHarmlessBasicBlock(std::vector<BasicBlock *> &HarmlessBB) {
    //get the largest, at least two instruction
    int size = 1;
    BasicBlock *LargestBB = nullptr;
    for (uint i = 0; i < HarmlessBB.size(); i++) {
        if (HarmlessBB.at(i)->size() > size) {
            size = HarmlessBB.at(i)->size();
            LargestBB = HarmlessBB.at(i);
        }
    }
    return LargestBB;
}

void Fus::getHarmlessBasicBlocks(Function *F, std::vector<BasicBlock *> &HarmlessBB) {
    Instruction *InsertPoint = &F->getEntryBlock().front();
    auto const &HarmnessMap = getAnalysis<HarmnessAnalysis>()
                          .getHarmnessMap();
    for (BasicBlock &BB : *F) {
        if (HarmnessMap.count(&BB) && HarmnessMap.lookup(&BB) == 0
            && BB.size() > 1) {
            bool BBMeanful = false;
            for (auto &Inst : BB) {
                if (!isa<PHINode>(&Inst) && !isa<BranchInst>(&Inst)
                    && !isa<ReturnInst>(&Inst)) {
                    BBMeanful = true;
                    break;
                }
            }
            for (auto &Inst : BB) {
                if (isa<SwitchInst>(&Inst)) {
                    // switch can not be merged
                    BBMeanful = false;
                    break;
                }
            }
            if (BBMeanful) {
                HarmlessBB.push_back(&BB);
            }
        }
    }
}

// key: values need phi
// value: instructions use the key
void Fus::getValuesNeedPHI(BasicBlock *Root, std::map<Value*, SetVector<Instruction*>*> &Values) {
    DT = &getAnalysis<DominatorTreeWrapperPass>(*FusionFunction).getDomTree();
    for (auto &BB : *FusionFunction) {
        // it says that bb does not dominate itself, but we still added this check
        if (&BB == Root)
            continue;
        if (DT->dominates(Root, &BB)) {
            for (auto &Inst : BB) {
                // for all the instructions root dominates,
                // all its operands should be dominated by the root after deep fusion
                // if it does't, it will break the SSA form, eg
                //       defBB
                //      /    \
                //     xx    yy
                //      \    /
                //       root
                //        |
                //       useBB
                // after deep fusion it would be
                //            ctrlBB
                //           /     \
                //       defBB      ...
                //      /    \      ...
                //     xx    yy     ...
                //        \    \    /
                //            root'
                //            /  \
                //        useBB   ...
                // defBB does not domanites useBB
                // so we need to add phis in root', now we just record what should be added.
                if (isa<BranchInst>(&Inst)) continue;
                uint OperandNum = Inst.getNumOperands();
                Value * Opi;
                for (uint i = 0; i < OperandNum; i++) {
                    Opi = Inst.getOperand(i);
                    // if (isa<Constant>(Opi)) continue;
                    if (Instruction *OpInst = dyn_cast<Instruction>(Opi)) {
                        BasicBlock *DefBB = OpInst->getParent();
                        if (DefBB == Root) continue;
                        if (!DT->dominates(Root, DefBB)) {
                            // this operand is defined before root bb, which needs a phi
                            // we record this instruction and the value
                            // which will be used when adding phis and replaceUseOfWith
                            SetVector<Instruction*> *UseInsts;
                            if (Values.find(Opi) != Values.end()) {
                                // we already know, record this use inst
                                UseInsts = Values[Opi];
                            } else {
                                // new a set, record this use Inst
                                UseInsts = new SetVector<Instruction*>();
                                Values[Opi] = UseInsts;
                            }
                            if (!UseInsts->count(&Inst)) {
                                UseInsts->insert(&Inst);
                            }
                        }
                    }
                }
            }
        }
    }
}

void Fus::moveAllocas() {
    std::vector<Instruction*> toMove;
    for (BasicBlock &BB : *FusionFunction) {
        for (Instruction &I : BB) {
            if (isa<AllocaInst>(I)) {
                toMove.push_back(&I);
            }
        }
    }
    Instruction *InsertPoint = &FusionFunction->getEntryBlock().front();
    while (!toMove.empty())
    {
        Instruction *I = toMove.back();
        toMove.pop_back();
        I->moveBefore(InsertPoint);
        InsertPoint = I;
    }
}

void Fus::insertOpaquePredict(BasicBlock *from, BasicBlock * to, bool IsFirst) {
    BasicBlock::iterator i1 = from->begin();
    if (from->getFirstNonPHIOrDbgOrLifetime()) {
        i1 = (BasicBlock::iterator)from->getFirstNonPHIOrDbgOrLifetime();
    }
    Twine *var = new Twine("originalBB");
    BasicBlock *originalBB = from->splitBasicBlock(i1, *var);

    // we modify the terminators to adjust the control flow.
    from->getTerminator()->eraseFromParent();

    // prepare a trampline BB, for the ssa form, the branch will go to here first
    // record the to bb in its instruction
    TrampolineID++;
    std::string ToName("deep_to");
    ToName.append(itostr(TrampolineID));
    StringRef BBName(ToName.c_str());
    to->setName(BBName);
    assert(to->getName().equals(BBName) && "Name set failed!\n");

    std::string AsmStr("nop #");
    AsmStr.append(to->getName().str());
    
    std::string TrampolineName("deep_trampoline");
    TrampolineName.append(itostr(TrampolineID));
    BasicBlock *TrampolineBB = BasicBlock::Create(*C, TrampolineName, FusionFunction);
    FunctionType *AsmTy = FunctionType::get(VoidTy, {}, false);
    Value * Nop = InlineAsm::get(AsmTy, AsmStr, "", false);
    CallInst *TrampolineCall = CallInst::Create(Nop, {}, "", TrampolineBB);
    BlockAddress *TrampolineAddress = BlockAddress::get(TrampolineBB);
    IndirectBrInst::Create(TrampolineAddress, 1, TrampolineBB);
    
    // The always true condition. End of the first block
    // For now, the condition is (x * (x + 1) % 2 == 0)
    // always-true
    FunctionType *RandomFuncTy = FunctionType::get(Int8Ty, {Int8Ty}, false);
    Function *RandomFunc = cast<Function>(MM->getOrInsertFunction("get_random", RandomFuncTy).getCallee());
    Value *Ctrl = FusionFunction->getArg(0);
    CallInst *X = CallInst::Create(RandomFunc, {Ctrl}, "", from);

    Twine *var4 = new Twine("condition");
    ICmpInst *condition = nullptr;
    if (IsFirst) {
        condition = new ICmpInst(*from, ICmpInst::ICMP_EQ, X,
                                       (Value*)ConstantInt::get(Int8Ty, 0), *var4);
    } else {
        condition = new ICmpInst(*from, ICmpInst::ICMP_NE, X,
                                       (Value*)ConstantInt::get(Int8Ty, 0), *var4);
    }
    // Jump to the original basic block if the condition is true or
    // to the toBB if false.
    BranchInst::Create(originalBB, TrampolineBB, (Value *)condition, from);
}

void Fus::replaceAliasUsers(Function *Old) {
    // check if Old's users contain GlobalAlias, if true, replace it with old and delete it.
    SmallVector<GlobalAlias *, 4> GlobalAliasToKill;
    for (auto user : Old->users()) {
        // direct use
        if (GlobalAlias *GA = dyn_cast<GlobalAlias>(user)) {
            // // errs() << "GlobalAlia\n";
            GA->replaceAllUsesWith(Old);
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
    for (Module::alias_iterator ai = MM->alias_begin(), ae = MM->alias_end(); ai != ae; ai++) {
        GlobalAlias *GA = &*ai;
        Constant *aliasee = GA->getAliasee();
        if (aliasee) {
            if(BitCastOperator * BO = dyn_cast<BitCastOperator>(aliasee)) {
                if(BO->getOperand(0) == Old) {
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
void Fus::replaceDirectCallers(Function *Old, Function *New, bool IsFirst) {
    bool oldFuncRetVoid = Old->getReturnType()->isVoidTy();
    std::vector<CallBase *> CallUsers;
    getCallInstBySearch(Old, CallUsers);
    for (uint i = 0; i < CallUsers.size(); i++) {
        CallSite CS(CallUsers.at(i));
        Instruction *I = CS.getInstruction();
        Function *EmptyOld = nullptr;
        BasicBlock *EmptyBB = nullptr;
        SmallVector<Value*, 4> NewArgs;
        arrangeArgList(EmptyOld, EmptyBB, CS, NewArgs, IsFirst);
        bool noUse = oldFuncRetVoid || I->user_empty();
        ArrayRef<Value *> NewArgsArr(NewArgs);
        // Whether the origin callbase is a callinst or an invokeinst,
        // we should replace it with corresponding instruction.
        Type *OldReturnType = Old->getReturnType();
        Value * target = nullptr;
        if (CallInst *CI = dyn_cast<CallInst>(I)) {
            CallInst *NewCallInst = CallInst::Create(New, NewArgsArr, "", I);
            NewCallInst->setCallingConv(New->getCallingConv());
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
            InvokeInst *NewInvoke = InvokeInst::Create(New->getFunctionType(), New, NormalDest,
                                II->getUnwindDest(), NewArgsArr, "", I);
            NewInvoke->setCallingConv(New->getCallingConv());
            target = NewInvoke;
            if (!noUse) {
                if (I->getType() != NewInvoke->getType()) {
                     // We need insert a new normal dest bb for return value bitcast
                    BasicBlock *ReturnBB = BasicBlock::Create(*C, "invoke.ret.trampoline.normal", II->getParent()->getParent(), NormalDest);
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
        assert(I->getNumUses() == 0 && "Old direct CallInst should not be used any more!");
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

Value *Fus::getExactValue(Value * value) {
    if (BitCastOperator * BO = dyn_cast<BitCastOperator>(value)) {
        return getExactValue(BO->getOperand(0));
    } else if (GlobalAlias *GA = dyn_cast<GlobalAlias>(value)){
        return getExactValue(GA->getAliasee());
    } else {
        return value;
    }
}

void Fus::getCallInstBySearch(Function *Old, std::vector<CallBase *> &CallUsers) {
    for (auto &F : *MM) {
        for (auto &BB : F) {
            for (auto &Inst : BB) {
                if (CallBase *CB = dyn_cast<CallBase>(&Inst)) {
                    Value * Callee = CB->getCalledValue();
                    if (isa<Function>(Callee)) {
                        if (Callee == Old) {
                            CallUsers.push_back(CB);
                        }
                    } else if (isa<BitCastOperator>(Callee)){
                        Value *CalledValue = getExactValue(Callee);
                        if (CalledValue == Old) {
                            CallUsers.push_back(CB);
                        } else if (Function * CalleeFunction = dyn_cast<Function>(CalledValue)) {
                            if (CalleeFunction->isDeclaration() && CalleeFunction->getName() == Old->getName()) {
                                CallUsers.push_back(CB);
                            }
                        }
                    }
                }
            }
        }
    }
}

void Fus::replaceIndirectUsers(Function *Old, Function *New, bool IsFirst) {
    // check if there exist users of old function
    if (Old->getNumUses() == 0)
        return;
    Constant * NewConstant = llvm::ConstantExpr::getPtrToInt(New, Int64Ty);
    Constant *ctrlArg; // use the third and the fourth bits. the first bit is used for virtual, the second is used in exception handling
    if (IsFirst)
        ctrlArg = ConstantInt::get(Int64Ty, 0x8);
    else
        ctrlArg = ConstantInt::get(Int64Ty, 0xc);
    Constant *TagConstant = ConstantExpr::get(Instruction::Add, NewConstant, ctrlArg);

    TagConstant = ConstantExpr::getIntToPtr(TagConstant, Int8PtrTy);
    TagConstant = ConstantExpr::getPointerCast(TagConstant, Old->getType());
    Old->replaceAllUsesWith(TagConstant);
    assert(Old->getNumUses() == 0 && "unhandled user for old.");
}

void Fus::extractPtrAndCtrlBitAtICall(Module &M) {
    vector<CallBase*> IndirectCalls;
    for (auto &F : M) {
        for (auto &BB : F)
            for (auto &I : BB)
                if (CallBase *CB = dyn_cast<CallBase>(&I))
                    if (CB->isIndirectCall())
                        IndirectCalls.push_back(CB);
    }
        
    unsigned IndirectCallNum = IndirectCalls.size();
    if (IndirectCallNum)
    {
        LLVMContext &C = M.getContext();

        Type *Int8PtrTy = Type::getInt8PtrTy(C);
        Type *Int8Ty = Type::getInt8Ty(C);
        FunctionType *extractPtrValTy = FunctionType::get(Int8PtrTy, {Int8PtrTy}, false);
        Function *ExtractPtrVal = cast<Function>(M.getOrInsertFunction("extract_ptrval", extractPtrValTy).getCallee());
        FunctionType *extractCtrlBitTy = FunctionType::get(Int8Ty, {Int8PtrTy}, false);
        Function *ExtractCtrlBit = cast<Function>(M.getOrInsertFunction("extract_ctrlbit", extractCtrlBitTy).getCallee());
        FunctionType *extractCtrlSignTy = FunctionType::get(Int8Ty, {Int8PtrTy}, false);
        Function *ExtractCtrlSign = cast<Function>(M.getOrInsertFunction("extract_ctrlsign", extractCtrlSignTy).getCallee());
        for (unsigned i = 0; i < IndirectCallNum; i++)
        {
            CallBase *CB = IndirectCalls.at(i);
            
            Value *IndirectFunction = CB->getCalledOperand();
            
            Value *newVal = CastInst::CreatePointerCast(IndirectFunction, Int8PtrTy, "", CB);
            Value *ctrlSign = CallInst::Create(ExtractCtrlSign, newVal, "", CB);

            // Split the callbase into an independent BB.
            // PredBB ---> OrigCallBB ---> OrigTarBB
            // PredBB ---> OrigInvokeBB ---> NormalDestBB
            BasicBlock *PredBB = CB->getParent();
            
            BasicBlock *OrigCallBB = CB->getParent()->splitBasicBlock(CB);
            
            PredBB->getTerminator()->eraseFromParent();
            BasicBlock *OrigTarBB;
            if (isa<CallInst>(CB))
                OrigTarBB = OrigCallBB->splitBasicBlock(CB->getNextNode());
            else if (InvokeInst *II = dyn_cast<InvokeInst>(CB))
                OrigTarBB = II->getNormalDest();
            // Create NewCallBB and fixed the branch according to ctrlSign.
            // PredBB ---> OrigCallBB ---> OrigTarBB
            //   |                             |
            //   --------> NewCallBB ---------->
            BasicBlock *NewCallBB = BasicBlock::Create(C, "icall", OrigCallBB->getParent());
            ICmpInst *icmp = new ICmpInst(*PredBB,
                                            ICmpInst::ICMP_EQ,
                                            ctrlSign,
                                            ConstantInt::getNullValue(Int8Ty),
                                            "");
            BranchInst::Create(OrigCallBB, NewCallBB, icmp, PredBB);
            BranchInst::Create(OrigTarBB, NewCallBB);
            // Set call target for NewCallBB.
            Instruction *insPt = NewCallBB->getTerminator();
            Value *ctrlBit = CallInst::Create(ExtractCtrlBit, newVal, "", insPt);
            // Extract the function pointer.
            CallInst *ptrVal = CallInst::Create(ExtractPtrVal, newVal, "", insPt);
            // reorder the arguments
            SmallVector<Value*, 4> IntArgs, FloatArgs;
            SmallVector<Type*, 4> IntArgTypes, FloatArgTypes;
            // 1. old args
            unsigned argIdx = 0;// floatIndex = 0 intIndex = 0;
            Value* Argi;
            Type* ArgiType;
            // Value *BitCasti;
            for (argIdx = 0; argIdx < CB->arg_size(); argIdx++) {
                Argi = CB->getArgOperand(argIdx);
                ArgiType = Argi->getType();
                if (ArgiType->isFloatingPointTy()) {
                    FloatArgs.push_back(Argi);
                    FloatArgTypes.push_back(ArgiType);
                } else {
                    IntArgs.push_back(Argi);
                    IntArgTypes.push_back(ArgiType);
                }
            }
            // 2. merge arg list
            SmallVector<Value*, 4> NewArgs;
            SmallVector<Type*, 4> NewArgTypes;
            // ctrl bit
            NewArgs.push_back(ctrlBit);
            NewArgTypes.push_back(ctrlBit->getType());

            NewArgs.append(IntArgs.begin(), IntArgs.end());
            NewArgTypes.append(IntArgTypes.begin(), IntArgTypes.end());

            NewArgs.append(FloatArgs.begin(), FloatArgs.end());
            NewArgTypes.append(FloatArgTypes.begin(), FloatArgTypes.end());

            ArrayRef<Type *> NewArgTypesArr(NewArgTypes);
            FunctionType *ICalleeFunctionType = FunctionType::get(CB->getType(),
                                                            NewArgTypesArr, false);
            Value *ICalleeFunction = CastInst::CreatePointerCast(ptrVal, ICalleeFunctionType->getPointerTo(), "", insPt);
            ArrayRef<Value *> NewArgsArr(NewArgs);
            bool noUse = CB->getType()->isVoidTy() || CB->user_empty();
            if (isa<CallInst>(CB)) {
                Value * ICall = CallInst::Create(ICalleeFunction, NewArgsArr, "", insPt);
                if (!noUse) {
                    PHINode *phiForCall = PHINode::Create(CB->getType(), 2, "", &OrigTarBB->front());
                    CB->replaceAllUsesWith(phiForCall);
                    phiForCall->addIncoming(CB, OrigCallBB);
                    phiForCall->addIncoming(ICall, NewCallBB);
                }
            } else if (InvokeInst *II = dyn_cast<InvokeInst>(CB)) {
                BasicBlock *NormalDest = II->getNormalDest();
                BasicBlock *UnwindDest = II->getUnwindDest();
                InvokeInst *NewII = InvokeInst::Create(ICalleeFunction, NormalDest, UnwindDest, NewArgsArr, "", insPt);
                if (!noUse) {
                    BasicBlock *InvokePhiTrampoline = BasicBlock::Create(C, "invoke.phi.trampoline", II->getParent()->getParent());
                    PHINode *phiForInvoke = PHINode::Create(CB->getType(), 2, "", InvokePhiTrampoline);
                    II->replaceAllUsesWith(phiForInvoke);
                    phiForInvoke->addIncoming(II, OrigCallBB);
                    phiForInvoke->addIncoming(NewII, NewCallBB);
                    BranchInst::Create(NormalDest, InvokePhiTrampoline);
                    NewII->setNormalDest(InvokePhiTrampoline);
                    II->setNormalDest(InvokePhiTrampoline);
                    // For all phis in the normal dest, we should change the incoming block to trampoline.
                    for (auto &PI : NormalDest->phis()) {
                        PI.replaceIncomingBlockWith(OrigCallBB, InvokePhiTrampoline);
                    }
                    for (auto &PI : UnwindDest->phis()) {
                        PI.addIncoming(PI.getIncomingValueForBlock(OrigCallBB), NewCallBB);
                    }
                    for (auto *U : II->users()) {
                        Instruction *IU = cast<Instruction>(U);
                        if (IU->getParent() == UnwindDest) {
                            llvm_unreachable("UnwindDest has users of invoke.");
                        }
                    }
                } else {
                    for (auto &PI : NormalDest->phis()) {
                        PI.addIncoming(PI.getIncomingValueForBlock(CB->getParent()), NewCallBB);
                    }
                    for (auto &PI : UnwindDest->phis()) {
                        PI.addIncoming(PI.getIncomingValueForBlock(CB->getParent()), NewCallBB);
                    }
                }
                NewCallBB->getTerminator()->eraseFromParent();
            } else {
                llvm_unreachable("Invalid opcode or unhandled case!");
            }

        }
    }
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

// static RegisterPass<Fus> X("Fus", "Fus Pass");
INITIALIZE_PASS_BEGIN(Fus, "Fus",
                      "Fus Pass", false, false)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(BlockFrequencyInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_END(Fus, "Fus",
                    "Fus Pass", false, false)

ModulePass *llvm::createFusPass() {
    return new Fus();
}
