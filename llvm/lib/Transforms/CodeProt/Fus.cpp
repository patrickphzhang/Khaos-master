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

#include "llvm/Transforms/CodeProt/Utils.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/CodeProt/HarmnessAnalysis.h"
#include "llvm/Transforms/CodeProt/InterFunctionDeepFusionPrepare.h"
#include "llvm/IR/Verifier.h"

#define DEBUG_TYPE "Fus"

namespace {
    struct Fus : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        const string ProtName = PROTNAME_INTERFUSION;
        const int ProtRatio = RatioFus;
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
            // // errs() << "Fus con\n";
            initializeFusPass(*PassRegistry::getPassRegistry());
        }
            
        void getAnalysisUsage(AnalysisUsage &AU) const override {
            
            AU.addRequired<BlockFrequencyInfoWrapperPass>();
            // if (DeepLevel > 1) {
                // errs() << "deep level > 1\n";
                AU.addRequired<HarmnessAnalysis>();
                AU.addRequired<LoopInfoWrapperPass>();
                AU.addRequired<DominatorTreeWrapperPass>();
                // AU.addPreserved<DominatorTreeWrapperPass>();
                // AU.addRequired<InterFunctionDeepFusionPrepare>();
                AU.setPreservesAll();
            // }
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
        void insertTrampolineCall(Function *Old, Function *New, bool IsFirst,
                                    ValueToValueMapTy &VMap);
        // cleaning
        // bool AttributeInSet(Attribute::AttrKind kind);
    };

}

char Fus::ID = 0;
void Fus::insertTrampolineCall(Function *Old, Function *New, bool IsFirst,
                                                ValueToValueMapTy &VMap) {
    assert(Old->size() == 0 && "What happened? We have already clean the body of Old.");
    auto &Context = New->getContext();
    Module *M = New->getParent();
    BasicBlock *TrampolineBB = BasicBlock::Create(Context, Old->getName() + "_trampoline", Old);
    // arrange new arg list
    SmallVector<Value*, 4> IntArgs, FloatArgs, F1VectorArgs, F2VectorArgs, VectorArgs;
    // 1. old args
    unsigned argIdx = 0, floatIndex = 0, intIndex = 0, vectorIndex1 = 0, vectorIndex2 = 0;
    Value* Argi;
    Type* ArgiType;
    Value *BitCasti;
    for (argIdx = 0; argIdx < Old->arg_size(); argIdx++) {
        Argi = Old->getArg(argIdx);
        // // errs() << "ArgiType: ";
        ArgiType = Argi->getType();
        // ArgiType->dump();
        // Argi->dump();
        if (ArgiType->isFloatingPointTy()) {
            if (ArgiType != FloatParamTypes[floatIndex]) {
                // add a bit cast to argi
                // BitCasti = TruncInst::CreateFPCast(Argi, FloatParamTypes[floatIndex], "", I);
                // FloatArgs.push_back(BitCasti);
                Instruction::CastOps CastOp = CastInst::getCastOpcode(Argi,
                                                                false, FloatParamTypes[floatIndex], false);
                BitCasti = CastInst::Create(CastOp, Argi, FloatParamTypes[floatIndex], "", TrampolineBB);
                FloatArgs.push_back(BitCasti);
            } else {
                FloatArgs.push_back(Argi);
            }
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
                // // errs() << "adding a cast\n";
                // // errs() << "source type: ";
                // ArgiType->dump();
                // // errs() << "dest type: ";
                // IntParamTypes[intIndex]->dump();
                // note: should we consider the sign flag?
                // Since the fusion's param is merged(larger or equal),
                // we may need an s/z ext, we use sext for now.
                // BitCasti = CastInst::CreateIntegerCast(Argi, IntParamTypes[intIndex], true, "", I);
                if (IntParamTypes[intIndex]->isVectorTy()) {
                    // // errs() << "found vector type:\n";
                    // IntParamTypes[intIndex]->dump();
                }
                Instruction::CastOps CastOp = CastInst::getCastOpcode(Argi,
                                                                false, IntParamTypes[intIndex], false);
                BitCasti = CastInst::Create(CastOp, Argi, IntParamTypes[intIndex], "", TrampolineBB);
                IntArgs.push_back(BitCasti);
            } else {
                IntArgs.push_back(Argi);
            }
            intIndex++;
        }
    }
    // 2.null values
    for (; intIndex < IntParamTypes.size(); intIndex++) {
        IntArgs.push_back(Constant::getNullValue(IntParamTypes[intIndex]));
    }
    for (; floatIndex < FloatParamTypes.size(); floatIndex++) {
        FloatArgs.push_back(Constant::getNullValue(FloatParamTypes[floatIndex]));
    }
    VectorArgs.append(F1VectorArgs.begin(), F1VectorArgs.end());
    for (; vectorIndex1 < F1VectorParamTypes.size(); vectorIndex1++) {
        VectorArgs.push_back(Constant::getNullValue(F1VectorParamTypes[vectorIndex1]));
    }
    VectorArgs.append(F2VectorArgs.begin(), F2VectorArgs.end());
    for (; vectorIndex2 < F2VectorParamTypes.size(); vectorIndex2++) {
        VectorArgs.push_back(Constant::getNullValue(F2VectorParamTypes[vectorIndex2]));
    }
    // 3. merge arg list
    SmallVector<Value*, 4> NewArgs;
    // ctrl bit
    if (IsFirst)
        NewArgs.push_back(ConstantInt::get(Type::getInt8Ty(*C), 0));
    else
        NewArgs.push_back(ConstantInt::get(Type::getInt8Ty(*C), 1));
    NewArgs.append(IntArgs.begin(), IntArgs.end());
    NewArgs.append(FloatArgs.begin(), FloatArgs.end());
    NewArgs.append(VectorArgs.begin(), VectorArgs.end());

    // bool noUse = oldFuncRetVoid || I->user_empty();
    ArrayRef<Value *> NewArgsArr(NewArgs);
    
    // // errs() << "Direct callsite: \n";
    CallInst *NewCallInst = CallInst::Create(New, NewArgsArr, "", TrampolineBB);
    NewCallInst->setCallingConv(New->getCallingConv());
            // if (CI->isTailCall()) {
            //     NewCallInst->setTailCall(true);
            // }
    Type *OldReturnType = Old->getReturnType();
    if (!OldReturnType->isVoidTy()) {
        if (OldReturnType != NewCallInst->getType()) {
            // if (OldReturnType->isVectorTy() || OldReturnType->isAggregateType()) {
            //     CastInst * ReturnCastInst = CastInst::CreateBitOrPointerCast(NewCallInst, OldReturnType->getPointerTo(), "", TrampolineBB->back());
            //     LoadInst *Pointer = new LoadInst(ReturnCastInst, "", TrampolineBB);
            //     ReturnInst::Create(M->getContext(), Pointer, TrampolineBB);
            // } else {
            Instruction::CastOps CastOp = CastInst::getCastOpcode(NewCallInst,
                                                            false, OldReturnType, false);
            Value *BitCast = CastInst::Create(CastOp, NewCallInst, OldReturnType, "", TrampolineBB);
            ReturnInst::Create(M->getContext(), BitCast, TrampolineBB);
            // }
        } else {
            ReturnInst::Create(M->getContext(), NewCallInst, TrampolineBB);
        }
    } else {
        // return void
        ReturnInst::Create(M->getContext(), nullptr, TrampolineBB);
    }
}

bool Fus::runOnModule(Module &M) {
    // return false;
    // errs() << "Fus\n";
    // M.dump();
    // errs() << "Deep Fusion Level: " << DeepLevel << "\n";
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
    if (DeepLevel > 1 && !EnableInterFunctionShuffleOptPass) {
        DeepFusionMode = true;
    }
    for (auto &F : *MM) {
        if (F.isCreatedByCodeProt()) {
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
    // // errs() << "functions may propagate:\n";
    // for (auto func : FuncsMayPropagate) {
    //     // errs() << func->getName() << "\n";
    // }
    for (auto &F : M) {
        // LBM_storeVelocityField and LBM_compareVelocityField
        // _ZN9regmngobj13createregionsEi_ZN9regmngobj19defineneighborhood1EvFusion
        // _ZN9regmngobj13defineregionsEv_ZN15largesolidarrayIP6regobjE8doublingEvFusion
        // _ZN9regmngobj7loadmapEPKc_ZN9regmngobj7initmapEiiFusion
        // getDpbSize and init_dpb
        // _ZN6soplex12SPxParMultPRD0Ev and _ZNK6soplex6SoPlex23qualConstraintViolationERdS1_
        // _ZN6cEnvir5setupEiPPc and _ZN6cEnvir3runEv
        // _ZN7cModuleC2EPKcPS_ and _ZN7cModuleD2Ev
        // _ZN11cSimulationD2Ev and _ZN11cSimulation13deleteNetworkEv | 471 segv todo
        // _ZN16ExecuteOnStartupC2EPFvvE and _ZN16ExecuteOnStartupD2Ev | 471 atexit arg is a bitcast and this bitcast is used multi times
        // _ZL8_do_listP7cObjectbRSo and _ZN7cObjectnwEm 
        // _ZN16ExecuteOnStartupD2Ev and _ZN16ExecuteOnStartup10executeAllEv
        // _ZN12pov_frontend13MessageOutput8InitInfoEP9POVMSDataS2_i and _ZN12pov_frontend13MessageOutput13RenderOptionsEP9POVMSDataS2_i
        // _ZN3pov8f_bicornEPdj and _ZN3pov9f_bifoliaEPdj
        // _ZNSt6vectorI5PointILi3EESaIS1_EE14_M_fill_insertEN9__gnu_cxx17__normal_iteratorIPS1_S3_EEmRKS1_ and _ZNSt6vectorIS_IS_IdSaIdEESaIS1_EESaIS3_EE14_M_fill_insertEN9__gnu_cxx17__normal_iteratorIPS3_S5_EEmRKS3_
        // _ZN10cMessage30C2ERKS__delete_notnull_i and _ZN10cMessage30C2ERKS__eh_resume
        // LBM_storeVelocityField LBM_compareVelocityField 
        // read_gauge_hdr and r_serial
        // _ZThn352_N6soplex9SPxSolverD1Ev and _ZThn352_N6soplex9SPxSolverD0Ev
        // merging _ZNSt22__uninitialized_fill_nILb0EE15__uninit_fill_nIP6VectorIdEmS3_EET_S5_T0_RKT1_ and _ZN25CompressedSparsityPatternC2Ejj
        // merging default_bzalloc and BZ2_bzWriteOpen
        // merging save_parallel and save_checkpoint
        // quantum_set_decoherence and quantum_hadamard
        // merging _ZN6soplex6SoPlex11enterVectorERKNS_5SPxIdE and _ZN8MySoPlexD0Ev
        // pec_fread and spec_getc
        // merging Perl_pp_binmode and Perl_pp_untie
        // merging change_address_1 and constant_subword
        // merging print_operand_address and output_387_binary_op
        // merging read_v3_gauge_hdr and parallel_open
        // merging get_i and qcdhdr_get_hdr
        // merging _ZN8LargeLAN13doBuildInsideEv_invoke_cont1963 and _ZN9MediumLAN13doBuildInsideEv_invoke_cont1281
        // merging init_c_lex_land_lhs_true and cb_file_change_if_then28
        // Init_QMatrix_extracted.18 and CalculateQuantParam
        // merging Configure_extracted.244 and GetConfigFileContent
        // merging Configure_entry_while_body_i_crit_edge and GetConfigFileContent
        // _ZN9FastBoard15nbr_criticalityEii and _ZNSt6vectorIhSaIhEE17_M_default_appendEm
        // merging _ZN6dealii8internal8DoFTools12_GLOBAL__N_134ensure_existence_of_subface_matrixILi3ELi3EEEvRKNS_13FiniteElementIXT_EXT0_EEES7_jRN5boost10shared_ptrINS_10FullMatrixIdEEEE and _ZN6dealii8internal8DoFTools12_GLOBAL__N_118filter_constraintsERKSt6vectorIjSaIjEES7_RKNS_10FullMatrixIdEERNS_16ConstraintMatrixE
        // merging _ZN6dealii11SolverGMRESINS_6VectorIdEEE5solveINS_12SparseMatrixIdEENS_9SparseILUIdEEEEvRKT_RS2_RKS2_RKT0_ and _ZN6dealii11SolverGMRESINS_6VectorIdEEED0Ev
        // merging _ZN9EnvirBase15checkTimeLimitsEv and _ZN9EnvirBase31stoppedWithTerminationExceptionER21cTerminationException
        // TODO: this is a bug, fix it
        if (F.getName().startswith("sha_crypt") || F.getName().startswith("OPENSSL_cpuid_setup"))
            continue;
        if (F.getName().startswith("wc_lines_avx2") || F.getName().startswith("__warn_memset_zero_len"))
            continue;
        // gl_dynarray_resizeFusion
        if (F.isIntrinsic() || F.isDeclaration() || F.isVarArg())
            continue;
        if (FissionedFunctionOnly && !F.isCreatedByCodeProt()) {
            // // errs() << "FissionedFunctionOnly && !F.isCreatedByCodeProt()\n";
            // // errs() << F.getName() << "\n";
            continue;
        }
        if (OriginFunctionOnly 
            && (F.isCreatedByCodeProt() || FuncsHasBeenFissioned.count(&F))) {
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
            || F.getName().find("get_random") != StringRef::npos)
            continue;
        TotalCount++;
        // function SolverGMRES::solve can not be processed, both fusion or fission
                                    // _ZN6dealii8SolverCG    INS_6VectorIdEEE5solveINS_12SparseMatrixIdEENS_16PreconditionSSORIS6_EEEEvRKT_RS2_RKS2_RKT0_
                                    //_ZN6dealii11SolverGMRES
        if (F.getName().contains("INS_6VectorIdEEE5solveIN")
            || F.getName().equals("_ZN9EnvirBase15checkTimeLimitsEv")
            || F.getName().startswith("_ZN9TOmnetApp15checkTimeLimitsEv")
            || F.getName().equals("ci_compare")
            /*|| (F.isCreatedByCodeProt() && F.getName().startswith("globextend_extracted"))*/) {
            // errs() << "skipping unfusionable function\n";
            continue;
        }
        // if (!F.getName().equals("cal_file_if_end2_split") && !F.getName().equals("log"))
        //     continue;
        if (FuncsMayPropagate.count(&F)) {
            // errs() << "FuncsMayPropagate: " << F.getName() << "\n";
            continue;
        }
        bool MayVarArg = false;
        for (auto user : F.users()) {
            if (Operator *OperatorUser = dyn_cast<Operator>(user)) {
                Type *TargetType = OperatorUser->getType();
                if (PointerType *TargetPointerType = dyn_cast<PointerType>(TargetType)) {
                    if (FunctionType *TargetFunctionType = dyn_cast<FunctionType>(TargetPointerType->getElementType())) {
                        if (TargetFunctionType->getFunctionNumParams() > F.arg_size()) {
                            // errs() << F.getName() << " MayVarArg\n";
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
                    // errs() << "We do not merge struct arg type for now\n";
                    // errs() << F.getName() << "\n";
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
    // for (Module::global_iterator gi = M.global_begin(); gi != M.global_end(); gi++) {
    //     GlobalVariable *GV = &*gi;
    //     if (GV && !GV->use_empty() && GV->hasInitializer()) {
    //         // // errs() << "build " << GV->getName() << "\n";
    //         buildFunctionReferenceMap(GV->getInitializer(), 0, GV, GV);
    //     }            
    // }

    // // errs() << "IntFuncsToFusion: " << IntFuncsToFusion.size() << "\n";
    // // errs() << "FloatFuncsToFusion: " << FloatFuncsToFusion.size() << "\n";
    // M.dump();
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
        // if (MergeCount < 3309)
        //     continue;
        // if (MergeCount >= 3310)
        //     continue;
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
        // M.dump();
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
                    //outs() << "add bit cast for float\n";
                    // Casti = TruncInst::CreateFPCast(FusionFunction->getArg(indexFloat),
                    //                 Argi->getType(), "", BitCastForF2);
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

            // if (deepFusionLevel1(VMap, F1, F2, true)) {
            //     // good, this one is succeed, record it
            //     FusionFunctionBK = CloneFunction(FusionFunction, BKVMap);
            // } else {
            //     // roll back
            //     // errs() << "deepFusionLevel1 failed\n";
            //     FusionFunction->replaceAllUsesWith(FusionFunctionBK);
            //     FusionFunction->dropAllReferences();
            //     FusionFunction->eraseFromParent();
            //     FusionFunction = FusionFunctionBK;
            //     // re-clone
            //     FusionFunctionBK = CloneFunction(FusionFunction, BKVMap);
            // }
            // // step 2, level 1 for F2->F1
            // BKVMap.clear();
            // if (deepFusionLevel1(VMap, F2, F1, false)) {
            //     // good, this one is succeed, record it
            //     FusionFunctionBK = CloneFunction(FusionFunction, BKVMap);
            // } else {
            //     // roll back
            //     // errs() << "deepFusionLevel1 failed\n";
            //     FusionFunction->replaceAllUsesWith(FusionFunctionBK);
            //     FusionFunction->dropAllReferences();
            //     FusionFunction->eraseFromParent();
            //     FusionFunction = FusionFunctionBK;
            //     // re-clone
            //     FusionFunctionBK = CloneFunction(FusionFunction, BKVMap);
            // }
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
        FusionFunction->setCreatedByCodeProt(true);
        FusionFunction->setDSOLocal(true);
        // // errs() << "Fusion successed\n";
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
        // // errs() << "replaceDirectCallers done\n";
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
    // FusionFunction->dump();
    // for (auto it = ArgSizeCount.begin(), ie = ArgSizeCount.end(); it != ie; it++) {
    //     uint ArgSize = it->first;
    //     uint Count = it->second;
    //     // errs() << ArgSize << ": " << Count << "\n";
    // }
    // ArgSizeCount.clear();
    // // errs() << "fusion done\n";
    // for (auto it = FusionArgSizeCount.begin(), ie = FusionArgSizeCount.end(); it != ie; it++) {
    //     uint ArgSize = it->first;
    //     uint Count = it->second;
    //     // errs() << ArgSize << ": " << Count << "\n";
    // }
    // FusionArgSizeCount.clear();
    if (!FissionedFunctionOnly) {
        extractPtrAndCtrlBitAtICall(M);
    }
    // 
    
    BeginDebug = false;
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
        // CB->dump();
        CallSite CS(CB);
        Value* Argi;
        for (unsigned argIdx = 0; argIdx < CS.arg_size(); argIdx++) {
            Argi = getExactValue(CS.getArgument(argIdx));
            if (Function * func = dyn_cast<Function>(Argi)) {
                // // errs() << "propagate function pointer: " << func->getName() << "\n";
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
    // Function *theSecond = set.front();
    // set.remove(theSecond);
    // theTwoToFusion = make_pair(theFirst, theSecond);
    // // Once we remove one element, the size of set varies too.
    // return theTwoToFusion;
    // // errs() << "first: " << theFirst->getName() << "\n";
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
        // // errs() << "second: " << theSecond->getName() << "\n";
        // if (FissionedFunctionOnly) {
            // // errs() << "theFirst->getOriginNameLength(): " << theFirst->getOriginNameLength() << "\n";
            // // errs() << "theSecond->getOriginNameLength(): " << theSecond->getOriginNameLength() << "\n";
        StringRef F1OriginName = theFirst->getOriginNameLength() > 0 ? theFirst->getName().substr(0, theFirst->getOriginNameLength()) : theFirst->getName();
        StringRef F2OriginName = theSecond->getOriginNameLength() > 0 ? theSecond->getName().substr(0, theSecond->getOriginNameLength()) : theSecond->getName();
        // // errs() << "F1 origin: " << F1OriginName << "\n";
        // // errs() << "F2 origin: " << F2OriginName << "\n";
        if (F1OriginName == F2OriginName) {
            // // errs() << "these two belong's to one function, choose another function.\n";
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
    //outs() << "collectFunctionParams: " << F->getName() << "\n";
    Argument *Argi;
    Type * ArgiType;
    for (uint i = 0; i < F->arg_size(); i++) {
        Argi = F->getArg(i);
        // Copied from other's code.
        if (VMap.count(Argi) != 0)
            continue;
        ArgiType = Argi->getType();
        //ArgiType->dump();
        if (ArgiType->isFloatingPointTy()) {
            FloatParamTypes.push_back(ArgiType);
            // // We meet a float type param, check if we can reuse old params.
            // if (indexFloat >= FloatParamNames.size())
            // {
            //     // We need to add a new float param
            //     FloatParamNames.push_back(string("argf_").append(itostr(indexFloat)));
            //     outs() << "argf_" << indexFloat << "\n";
            // }
            // indexFloat++;
        }
        else if (ArgiType->isVectorTy()) {
            VectorParamTypes.push_back(ArgiType);
        }
        else {
            IntParamTypes.push_back(ArgiType);
            // // We meet a int type param, check if we can reuse old params.
            // if (indexInt >= IntParamNames.size())
            // {
            //     // We need to add a new int param
            //     IntParamNames.push_back(string("argi_").append(itostr(indexInt)));
            //     outs() << "argi_" << indexInt << "\n";
            // }
            // indexInt++;
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
    // // errs() << "moveFunction\n";
    LLVMContext &C = M->getContext();
    const DataLayout &DL = M->getDataLayout();
    SmallVector<ReturnInst*, 8> Returns;
    ClonedCodeInfo *CodeInfo = nullptr;
    unsigned oldBBNum = DestFunction->size();
    CloneFunctionInto(DestFunction, SrcFunction, VMap, true, Returns, "",
                    CodeInfo);
    // // errs() << "moveFunction done\n";
    // DestFunction->dump();
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
                        // // errs() << SrcFunction->getName() << "\n";
                        // // errs() << "OldReturnType: ";
                        // OldReturnType->dump();
                        // // errs() << "OldReturnType: " << OldReturnType->isAggregateType() << OldReturnType->isVectorTy() << "\n";
                        // // errs() << "DestReturnType: ";
                        // DestReturnType->dump();
                        // // errs() << "DestReturnType: " << DestReturnType->isAggregateType() << DestReturnType->isVectorTy() << "\n";
                        if (OldReturnType != DestReturnType) {
                            // add a bitcast
                            Value * NewRetValue;
                            if (OldReturnType->isVectorTy() || OldReturnType->isAggregateType()) {
                                // we need to create a pointer to than return value
                                // RetValue->getType()->dump();
                                // // errs() << "OldReturnType is Aggregate or Vector: " << OldReturnType->isAggregateType() << OldReturnType->isVectorTy() << "\n";
                                assert("OldReturnType is Aggregate or Vector");
                                AllocaInst *Pointer = new AllocaInst(OldReturnType, DL.getAllocaAddrSpace(), "", RI);
                                new StoreInst(RetValue, Pointer, RI);
                                Instruction::CastOps CastOp = CastInst::getCastOpcode(Pointer,
                                                                        false, DestReturnType, false);
                                NewRetValue = CastInst::Create(CastOp, Pointer, DestReturnType, "", RI);
                                // NewRetValue->dump();
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
    // // errs() << "deep fusion level 1\n";
    // we do not handle exception irrelevent function
    if (isEHRelatedFunction(from)) {
        return;
    }
    unsigned idxFrom = rand() % (from->size()/2 + from->size()%2);
    unsigned idxTo = rand() % (to->size());
    // // errs() << "idxFrom: " << idxFrom << "\n";
    // // errs() << "idxTo: " << idxTo << "\n";
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
    if (fromBB && toBB) {
        // fromBB->dump();
        // toBB->dump();
        insertOpaquePredict(fromBB, toBB, IsFirst);
    } else {
        // errs() << "Can not find the corresponding bb in fusion function.\n";
    }
    // return !verifyFunction(*FusionFunction);
}

bool Fus::deepFusionLevel2(ValueToValueMapTy &VMap) {
    // // errs() << "deep fusion level 2\n";
    // F1->dump();
    // F2->dump();
    // FusionFunction->dump();
    // 0. merge all the allocas to the Fusion's entry
    moveAllocas();
    // 1. find a mergable pair of basic blocks from f1 and f2
    std::vector<BasicBlock *> HarmlessBBF1, HarmlessBBF2;
    getHarmlessBasicBlocks(F1, HarmlessBBF1);
    getHarmlessBasicBlocks(F2, HarmlessBBF2);
    
    if (HarmlessBBF1.size() == 0 || HarmlessBBF1.size() == 0) {
        // errs() << "no harmless basic block found, return\n";
        return true;
    }
    outs() << "STATISTICS: HarmlessBB count" << HarmlessBBF1.size() << " " << HarmlessBBF2.size() << "\n";
    BasicBlock *BBF1 = getOneHarmlessBasicBlock(HarmlessBBF1);
    BasicBlock *BBF2 = getOneHarmlessBasicBlock(HarmlessBBF2);
    if (BBF1 == nullptr || BBF2 == nullptr) {
        // // errs() << "no suitable harmless basic block found, return\n";
        return true;
    }
    outs() << "STATISTICS: HarmlessBB size" << BBF1->size() << " " << BBF2->size() << "\n";
    // BBF1->dump();
    // BBF2->dump();
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
        // // errs() << "We cannot merge entry BB\n";
        return true;
    }
    for (BasicBlock *Pred : predecessors(BB1)) {
        if (Pred == &FusionFunction->getEntryBlock()) {
            for (BasicBlock *Pred2 : predecessors(BB2)) {
                if (Pred2 == &FusionFunction->getEntryBlock()) {
                    // this means we are merging entry BB's successor, which is meaningless
                    // errs() << "We won't merge entry BB's successor\n";
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
    // FusionFunction->getParent()->dump();
    // // errs() << "deep fusion candidate:\n";
    // BB1->dump();
    // BB2->dump();
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
        // // errs() << "moving\n";
        // ToMove->dump();
        // BB2->dump();
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
                // // errs() << "adding phi for\n";
                // Opi->dump();
                PHINode *phi = PHINode::Create(Opi->getType(), 0, "", &BB2->front());
                for (BasicBlock *Pred : predecessors(BB1)) {
                   phi->addIncoming(Opi, Pred); 
                }
                for (BasicBlock *Pred : predecessors(BB2)) {
                   phi->addIncoming(Constant::getNullValue(Opi->getType()), Pred); 
                }
                // // errs() << "phi:\n";
                // phi->dump();
                ToMove->replaceUsesOfWith(Opi, phi);
                // // errs() << "after replace\n";
                // ToMove->dump();
                // BB2->dump();
            }
        }
    }
    // 7. add phis in BB2, these phis are needed because we changed the CFG
    for (auto it = ValuesNeedPHIForBB1.begin(), 
              ie = ValuesNeedPHIForBB1.end(); it != ie; it++) {
        Value *ValueNeedPHI = it->first;
        // // errs() << "this value needs phi\n";
        // ValueNeedPHI->dump();
        PHINode *phi = PHINode::Create(ValueNeedPHI->getType(), 0, "", &BB2->front());
        for (BasicBlock *Pred : predecessors(BB1)) {
            phi->addIncoming(ValueNeedPHI, Pred); 
        }
        for (BasicBlock *Pred : predecessors(BB2)) {
            phi->addIncoming(Constant::getNullValue(ValueNeedPHI->getType()), Pred); 
        }

        SetVector<Instruction*> *UseInsts = it->second;
        // // errs() << "they are using it\n";
        while (UseInsts->size()) {
            Instruction *UseInst = UseInsts->pop_back_val();
            // UseInst->dump();
            UseInst->replaceUsesOfWith(ValueNeedPHI, phi);
        }
    }
    for (auto it = ValuesNeedPHIForBB2.begin(), 
              ie = ValuesNeedPHIForBB2.end(); it != ie; it++) {
        Value *ValueNeedPHI = it->first;
        SetVector<Instruction*> *UseInsts = it->second;
        // // errs() << "this value needs phi\n";
        // ValueNeedPHI->dump();
        PHINode *phi = PHINode::Create(ValueNeedPHI->getType(), 0, "", &BB2->front());
        for (BasicBlock *Pred : predecessors(BB2)) {
            phi->addIncoming(ValueNeedPHI, Pred); 
        }
        for (BasicBlock *Pred : predecessors(BB1)) {
            phi->addIncoming(Constant::getNullValue(ValueNeedPHI->getType()), Pred); 
        }
        // // errs() << "they are using it\n";
        while (UseInsts->size()) {
            Instruction *UseInst = UseInsts->pop_back_val();
            // UseInst->dump();
            UseInst->replaceUsesOfWith(ValueNeedPHI, phi);
        }
    }
    // // errs() << "BB2:\n";
    // BB2->dump();
    BB1->replaceAllUsesWith(BB2);
    // BB1->dump();
    // BB2->dump();
    
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
    // // errs() << "BB2:\n";
    // BB2->dump();
    // FusionFunction->dump();
    // // errs() << "deep fusion level 2 done\n";
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
    // // errs() << "preprocessToMergable\n";
    // BB->dump();
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
        // // errs() << "before split return\n";
        // BB->dump();
        BB->splitBasicBlock(i1);
    }
    // // errs() << "after preprocess:\n";
    // BB->dump();
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
                // // errs() << "found a harmless bb\n";
                // BB.dump();
            }
        }
        // BB.dump();
        // bool Harmless = true;
        // for (Instruction &I : BB) {
        //     if (HarmnessMap.count(&I)) {
        //         if (HarmnessMap.lookup(&I) > 0)
        //             Harmless = false;
        //     } else Harmless = false;
        // }   
        // if (Harmless) {
        //     // && BB.size() > 1
        //     uint InstCount  = 0;
        //     for (auto &Inst : BB) {
        //         if (isa<BranchInst>(&Inst) || isa<PHINode>(&Inst)
        //             || isa<CmpInst>(&Inst) || isa<ReturnInst>(&Inst))
        //             continue;
        //         InstCount++;
        //     }
        //     if (InstCount > 0) {
        //         HarmlessBB.push_back(&BB);
        //         // // errs() << "found a harmless bb\n";
        //         // BB.dump();
        //     }
        // }
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
            // // errs() << "dominates\n";
            // BB.dump();
            // DominatorTreeBB.push_back(&BB);
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
                            // // errs() << "Operand needs a phi.\n";
                            // Opi->dump();
                            SetVector<Instruction*> *UseInsts;
                            if (Values.find(Opi) != Values.end()) {
                                // we already know, record this use inst
                                UseInsts = Values[Opi];
                            } else {
                                // new a set, record this use Inst
                                UseInsts = new SetVector<Instruction*>();
                                Values[Opi] = UseInsts;
                            }
                            // UseInsts->insert(&Inst);
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
                // I.moveAfter(InsertPoint);
                // InsertPoint = &I;
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
    // // errs() << "after set name: " << to->getName() << "\n";
    
    std::string TrampolineName("deep_trampoline");
    TrampolineName.append(itostr(TrampolineID));
    BasicBlock *TrampolineBB = BasicBlock::Create(*C, TrampolineName, FusionFunction);
    FunctionType *AsmTy = FunctionType::get(VoidTy, {}, false);
    Value * Nop = InlineAsm::get(AsmTy, AsmStr, "", false);
    CallInst *TrampolineCall = CallInst::Create(Nop, {}, "", TrampolineBB);
    // BranchInst::Create(TrampolineBB, TranpolineBB);
    // new UnreachableInst(*C, TrampolineBB);
    BlockAddress *TrampolineAddress = BlockAddress::get(TrampolineBB);
    IndirectBrInst::Create(TrampolineAddress, 1, TrampolineBB);
    
    // The always true condition. End of the first block
    // For now, the condition is (x * (x + 1) % 2 == 0)
    // always-true
    // Value *X = ConstantInt::get(Int8Ty, rand());
    FunctionType *RandomFuncTy = FunctionType::get(Int8Ty, {Int8Ty}, false);
    Function *RandomFunc = cast<Function>(MM->getOrInsertFunction("get_random", RandomFuncTy).getCallee());
    Value *Ctrl = FusionFunction->getArg(0);
    CallInst *X = CallInst::Create(RandomFunc, {Ctrl}, "", from);
    
    // Value *op = BinaryOperator::Create(Instruction::Add, X,
    //             (Value*)ConstantInt::get(Int8Ty, 1), "", from);

    // Value *op1 = BinaryOperator::Create(Instruction::Mul, X, op, "", from);
    
    // op = BinaryOperator::Create(Instruction::URem, op1, 
    //                             (Value*)ConstantInt::get(Int8Ty, 2), "", from);

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
    
    // adjust phis of the toBB
    // for (auto &PI : to->phis()) {
    //     // // errs() << "toBB->phis\n";
    //     // PI.dump();
    //     Type *type = PI.getType();
    //     PI.addIncoming(Constant::getNullValue(PI.getType()), from);
    // }
}

void Fus::replaceAliasUsers(Function *Old) {
    // // errs() << "replaceAliasUsers\n";
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
                // // errs() << "Bitcast alias\n";
                // GA->dump();
                if(BO->getOperand(0) == Old) {
                    // errs() << "indirect alisee is old func\n";
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
    // // errs() << "replaceDirectCallers\n";
    bool oldFuncRetVoid = Old->getReturnType()->isVoidTy();
    std::vector<CallBase *> CallUsers;
    getCallInstBySearch(Old, CallUsers);
    for (uint i = 0; i < CallUsers.size(); i++) {
        CallSite CS(CallUsers.at(i));
        Instruction *I = CS.getInstruction();
        // // errs() << "user " << i << "\n";
        // I->dump();
        // Function *UserFunction = I->getParent()->getParent();
        // UserFunction->dump();
        // arrange new arg list
        SmallVector<Value*, 4> IntArgs, FloatArgs, F1VectorArgs, F2VectorArgs, VectorArgs;
        // 1. old args
        unsigned argIdx = 0, floatIndex = 0, intIndex = 0, vectorIndex1 = 0, vectorIndex2 = 0;
        Value* Argi;
        Type* ArgiType;
        Value *BitCasti;
        for (argIdx = 0; argIdx < CS.arg_size(); argIdx++) {
            Argi = CS.getArgument(argIdx);
            // // errs() << "ArgiType: ";
            ArgiType = Argi->getType();
            // ArgiType->dump();
            // Argi->dump();

            if (ArgiType->isFloatingPointTy()) {
                // // errs() << "1\n";
                if (ArgiType != FloatParamTypes[floatIndex]) {
                    Instruction::CastOps CastOp = CastInst::getCastOpcode(Argi,
                                                                    false, FloatParamTypes[floatIndex], false);
                    BitCasti = CastInst::Create(CastOp, Argi, FloatParamTypes[floatIndex], "", I);
                    FloatArgs.push_back(BitCasti);
                } else {
                    FloatArgs.push_back(Argi);
                }
                floatIndex++;
            } else if (ArgiType->isVectorTy()) {
                if (IsFirst) {
                    assert(ArgiType == F1VectorParamTypes[vectorIndex1] && "DirectCaller ArgTy is VectorTy but not equals to origin");
                    F1VectorArgs.push_back(Argi);
                    vectorIndex1++;
                } else {
                    assert(ArgiType == F2VectorParamTypes[vectorIndex2] && "DirectCaller ArgTy is VectorTy but not equals to origin");
                    F2VectorArgs.push_back(Argi);
                    vectorIndex2++;
                }
            } else {
                // // errs() << "2\n";
                if (ArgiType != IntParamTypes[intIndex]) {
                    // // errs() << "4\n";
                    // add a bit cast to argi
                    // // errs() << "adding a cast\n";
                    // // errs() << "source type: ";
                    // ArgiType->dump();
                    // // errs() << "dest type: ";
                    // IntParamTypes[intIndex]->dump();
                    // note: should we consider the sign flag?
                    // Since the fusion's param is merged(larger or equal),
                    // we may need an s/z ext, we use sext for now.
                    // BitCasti = CastInst::CreateIntegerCast(Argi, IntParamTypes[intIndex], true, "", I);
                    if (IntParamTypes[intIndex]->isVectorTy()) {
                        // errs() << "4found vector type:\n";
                        // IntParamTypes[intIndex]->dump();
                    }
                    Instruction::CastOps CastOp = CastInst::getCastOpcode(Argi,
                                                                    false, IntParamTypes[intIndex], false);
                    BitCasti = CastInst::Create(CastOp, Argi, IntParamTypes[intIndex], "", I);
                    IntArgs.push_back(BitCasti);
                } else {
                    IntArgs.push_back(Argi);
                }
                intIndex++;
            }
        }
        // // errs() << "5\n";
        // 2.null values
        for (; intIndex < IntParamTypes.size(); intIndex++) {
            IntArgs.push_back(Constant::getNullValue(IntParamTypes[intIndex]));
        }
        // // errs() << "6\n";
        for (; floatIndex < FloatParamTypes.size(); floatIndex++) {
            FloatArgs.push_back(Constant::getNullValue(FloatParamTypes[floatIndex]));
        }
        VectorArgs.append(F1VectorArgs.begin(), F1VectorArgs.end());
        for (; vectorIndex1 < F1VectorParamTypes.size(); vectorIndex1++) {
            VectorArgs.push_back(Constant::getNullValue(F1VectorParamTypes[vectorIndex1]));
        }
        VectorArgs.append(F2VectorArgs.begin(), F2VectorArgs.end());
        for (; vectorIndex2 < F2VectorParamTypes.size(); vectorIndex2++) {
            VectorArgs.push_back(Constant::getNullValue(F2VectorParamTypes[vectorIndex2]));
        }
        // 3. merge arg list
        SmallVector<Value*, 4> NewArgs;
        // ctrl bit
        if (IsFirst)
            NewArgs.push_back(ConstantInt::get(Type::getInt8Ty(*C), 0));
        else
            NewArgs.push_back(ConstantInt::get(Type::getInt8Ty(*C), 1));
        NewArgs.append(IntArgs.begin(), IntArgs.end());
        NewArgs.append(FloatArgs.begin(), FloatArgs.end());
        NewArgs.append(VectorArgs.begin(), VectorArgs.end());
        // // errs() << "VectorArgs size: " << VectorArgs.size() << "\n";

        bool noUse = oldFuncRetVoid || I->user_empty();
        // outs() << "arglist type: \n";
        // for (uint i = 0; i < NewArgs.size(); i++) {
        //     NewArgs[i]->getType()->dump();
        // }
        // outs() << "New->getType()->dump(): ";
        // New->getType()->dump();
        ArrayRef<Value *> NewArgsArr(NewArgs);
        // Whether the origin callbase is a callinst or an invokeinst,
        // we should replace it with corresponding instruction.
        Type *OldReturnType = Old->getReturnType();
        if (CallInst *CI = dyn_cast<CallInst>(I)) {
            // // errs() << "Direct callsite: \n";
            // New->dump();
            // // errs() << "NewArgs: \n";
            // for (auto na : NewArgsArr) {
            //     na->dump();
            // }
            // // errs() << "NewArgs end\n";
            CallInst *NewCallInst = CallInst::Create(New, NewArgsArr, "", I);
            NewCallInst->setCallingConv(New->getCallingConv());
            // if (CI->isTailCall()) {
            //     NewCallInst->setTailCall(true);
            // }
            if (!noUse) {
                if (I->getType() != NewCallInst->getType()) {
                    if (OldReturnType->isVectorTy() || OldReturnType->isAggregateType()) {
                        CastInst * ReturnCastInst = CastInst::CreateBitOrPointerCast(NewCallInst, OldReturnType->getPointerTo(), "", I);
                        LoadInst *Pointer = new LoadInst(ReturnCastInst, "", I);
                        // Pointer->dump();
                        // Instruction::CastOps CastOp = CastInst::getCastOpcode(Pointer,
                        //                                         false, Old->getReturnType(), false);
                        // Value *NewRetValue = CastInst::Create(CastOp, Pointer, Old->getReturnType(), "", CI);
                        // NewRetValue->dump();
                        I->replaceAllUsesWith(Pointer);
                    } else {
                        Instruction::CastOps CastOp = CastInst::getCastOpcode(NewCallInst,
                                                                        false, I->getType(), false);
                        Value *BitCast = CastInst::Create(CastOp, NewCallInst, I->getType(), "", I);
                        I->replaceAllUsesWith(BitCast);
                    }
                } else {
                    I->replaceAllUsesWith(NewCallInst);
                }
            }
        } else if (InvokeInst *II = dyn_cast<InvokeInst>(I)) {
            BasicBlock *NormalDest = II->getNormalDest();
            BasicBlock *UnwindDest = II->getUnwindDest();
            InvokeInst *NewInvoke = InvokeInst::Create(New->getFunctionType(), New, NormalDest,
                                UnwindDest, NewArgsArr, "", I);
            NewInvoke->setCallingConv(New->getCallingConv());
            if (!noUse) {
                if (I->getType() != NewInvoke->getType()) {
                    // // errs() << "new case\n";
                    // II->getParent()->getParent()->dump();
                     // We need insert a new normal dest bb for return value bitcast
                    BasicBlock *ReturnBB = BasicBlock::Create(*C, "invoke.ret.trampoline.normal", II->getParent()->getParent(), NormalDest);
                    NewInvoke->setNormalDest(ReturnBB);
                    BranchInst::Create(NormalDest, ReturnBB);
                    Instruction *InsertPoint = ReturnBB->getFirstNonPHI();
                    // Value * PointerBitCastAlias;
                    if (OldReturnType->isVectorTy() || OldReturnType->isAggregateType()) {
                        CastInst * ReturnCastInst = CastInst::CreateBitOrPointerCast(NewInvoke, OldReturnType->getPointerTo(), "", InsertPoint);
                        LoadInst *Pointer = new LoadInst(ReturnCastInst, "", InsertPoint);
                        I->replaceAllUsesWith(Pointer);
                        // PointerBitCastAlias = Pointer;
                    } else {
                        Instruction::CastOps CastOp = CastInst::getCastOpcode(NewInvoke,
                                                                        false, I->getType(), false);
                        Value *BitCast = CastInst::Create(CastOp, NewInvoke, I->getType(), "", InsertPoint);
                        I->replaceAllUsesWith(BitCast);
                        // PointerBitCastAlias = BitCast;
                    }
                    // For all phis in the normal dest, we should change the incoming block to trampoline.
                    // PointerBitCastAlias->dump();
                    for (auto &PI : NormalDest->phis()) {
                            PI.replaceIncomingBlockWith(II->getParent(), ReturnBB);
                    }
                    // bool UsingRet = false;
                    // for (auto &PI : NormalDest->phis()) {
                    //     // errs() << "NormalDest->phis\n";
                    //     PI.dump();
                    //     unsigned Op = 0;
                    //     for (Value *IV : PI.incoming_values()) {
                    //         if (IV == PointerBitCastAlias) {
                    //             // errs() << "This normal phi is using return value, replace the incoming block.\n";
                    //             // this PHI uses return value, we replace the incoming block to trampoline
                    //             // PI.setIncomingBlock(Op, ReturnBB);
                    //             UsingRet = true;
                    //         }
                    //         Op++;
                    //     }
                    //     // PI.dump();
                    //     // PI.replaceIncomingBlockWith(II->getParent(), ReturnBB);
                    // }
                    // if (UsingRet) {
                    //      for (auto &PI : NormalDest->phis()) {
                    //         PI.replaceIncomingBlockWith(II->getParent(), ReturnBB);
                    //     }
                    // }
                    // UsingRet = false;
                    // for (auto &PI : UnwindDest->phis()) {
                    //     // errs() << "UnwindDest->phis\n";
                    //     PI.dump();
                    //     unsigned Op = 0;
                    //     for (Value *IV : PI.incoming_values()) {
                    //         if (IV == PointerBitCastAlias) {
                    //             // errs() << "This unwind phi is using return value, change to null.\n";
                    //             PI.replaceUsesOfWith(PointerBitCastAlias, Constant::getNullValue(PointerBitCastAlias->getType()));
                    //             // PI.setIncomingBlock(Op, ReturnBB);
                    //         }
                    //         Op++;
                    //     }
                    //     PI.dump();
                    //     // PI.addIncoming(PI.getIncomingValueForBlock(II->getParent()), ReturnBB);
                    // }
                    // if (UsingRet) {
                    //     for (auto &PI : UnwindDest->phis()) {
                    //         PI.replaceIncomingBlockWith(II->getParent(), ReturnBB);
                    //     }
                    // }
                    // // errs() << "after handle\n";
                    // II->getParent()->getParent()->dump();
                } else {
                    I->replaceAllUsesWith(NewInvoke);
                }
            }
        } else {
            llvm_unreachable("unhandled replace direct call\n");
        }
        assert(I->getNumUses() == 0 && "Old direct CallInst should not be used any more!");
        Value * OldCallee = I->getOperand(0);
        // 
        if (CallBase *CI = dyn_cast<CallBase>(I)) {
            OldCallee = CI->getCalledValue();
        }
        //
        I->eraseFromParent();
        //I->dropAllReferences();
        // // errs() << "trying to destory old callee\n";
        // OldCallee->dump();
        if (OldCallee->use_empty() && !isa<Function>(OldCallee)) {
            // // errs() << "OldCallee->use_empty()\n";
            if (User * OldCalleeAsUser = dyn_cast<User>(OldCallee)) {
                // // errs() << "It's a user\n";
                OldCalleeAsUser->dropAllReferences();
                // OldCalleeAsUser->deleteValue();
            } else {
                // // errs() << "Normal value\n";
                OldCallee->deleteValue();
            }
        } else {
            // // errs() << "someone still using old callee\n";
            // OldCallee->dump();
        }
        // UserFunction->dump();
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
    // // errs() << "getCallInstBySearch" << Old->getName() << "\n";
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
                    } else if (isa<GlobalAlias>(Callee)) {
                        // // errs() << "called alias\n";
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
    // errs() << "found " << IndirectCallNum << " indirect calls\n";
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
                // outs() << "ArgiType:\n";
                // ArgiType->dump();
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
                // // errs() << "Invoke inst\n";
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
