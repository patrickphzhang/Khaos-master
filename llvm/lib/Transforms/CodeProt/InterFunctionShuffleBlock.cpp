//===- InterFunctionShuffleBlock.cpp ------------------------------------- ---------------===//
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
#include "llvm/Transforms/CodeProt/CPCodeExtractor.h"

#define DEBUG_TYPE "block"

STATISTIC(NumExtracted, "Number of basic blocks extracted by InterFunctionShuffle");

namespace {
    struct InterFunctionShuffleBlock : public ModulePass {
        static char ID;
        const string ProtName = PROTNAME_INTERSHUFFLE;
        const int ProtRatio = RatioInterShuffle;
        SmallVector<SmallVector<BasicBlock *, 16>, 4> GroupsOfBlocks;
        Function* DebugFunction;
        /// Map a function name to groups of blocks.
        // SmallVector<std::pair<std::string, SmallVector<std::string, 4>>, 4> BlocksByName;
        SmallVector<std::pair<std::string, SmallSetVector<BasicBlock*, 4>>, 4> BlocksByName;

        vector<Function*> FissionFunction;

        InterFunctionShuffleBlock(const SmallVectorImpl<BasicBlock *> &BlocksToExtract) : ModulePass(ID){
            // We want one group per element of the input list.
            SmallVector<SmallVector<BasicBlock *, 16>, 4> MassagedGroupsOfBlocks;
            for (BasicBlock *BB : BlocksToExtract) {
                SmallVector<BasicBlock *, 16> NewGroup;
                NewGroup.push_back(BB);
                MassagedGroupsOfBlocks.push_back(NewGroup);
            }
            init(MassagedGroupsOfBlocks);
            initializeInterFunctionShuffleBlockPass(*PassRegistry::getPassRegistry());
        }
        InterFunctionShuffleBlock() : InterFunctionShuffleBlock(SmallVector<BasicBlock *, 0>()) {}

        void init(const SmallVectorImpl<SmallVector<BasicBlock *, 16>> &GroupsOfBlocksToExtract);
        void splitLandingPadPreds(Function &F);
        bool skipFunction(Function *F);

        bool runOnModule(Module &M) override;

        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.addRequired<DominatorTreeWrapperPass>();
            AU.addRequired<BlockFrequencyInfoWrapperPass>();
        }
        std::vector<uint64_t> getBlockFreqVec(Function &F);
    };
} // end anonymous namespace

char InterFunctionShuffleBlock::ID = 0;
    
void InterFunctionShuffleBlock::init(const SmallVectorImpl<SmallVector<BasicBlock *, 16>> &GroupsOfBlocksToExtract) {
    for (const SmallVectorImpl<BasicBlock *> &GroupOfBlocks : GroupsOfBlocksToExtract) {
        SmallVector<BasicBlock *, 16> NewGroup;
        NewGroup.append(GroupOfBlocks.begin(), GroupOfBlocks.end());
        GroupsOfBlocks.emplace_back(NewGroup);
    }
}


// return F's block frequency set, whose elements are in descending-order
std::vector<uint64_t> InterFunctionShuffleBlock::getBlockFreqVec(Function &F) {
    std::vector<uint64_t> blockFreqVec;
    BlockFrequencyInfo &BFI =
        getAnalysis<BlockFrequencyInfoWrapperPass>(F).getBFI();
    for (BasicBlock &bb : F) {
        blockFreqVec.push_back(BFI.getBlockFreq(&bb).getFrequency());
    }
    std::sort(blockFreqVec.begin(), blockFreqVec.end());
    std::reverse(blockFreqVec.begin(), blockFreqVec.end());
    return blockFreqVec;
}


/// Extracts the landing pads to make sure all of them have only one
/// predecessor.
void InterFunctionShuffleBlock::splitLandingPadPreds(Function &F) {
    for (BasicBlock &BB : F) {
        for (Instruction &I : BB) {
            if (!isa<InvokeInst>(&I)) continue;
            InvokeInst *II = cast<InvokeInst>(&I);
            BasicBlock *Parent = II->getParent();
            BasicBlock *LPad = II->getUnwindDest();

            // Look through the landing pad's predecessors. If one of them ends in an
            // 'invoke', then we want to split the landing pad.
            bool Split = false;
            for (auto PredBB : predecessors(LPad)) {
                if (PredBB->isLandingPad() && PredBB != Parent &&
                        isa<InvokeInst>(Parent->getTerminator())) {
                    Split = true;
                    break;
                }
            }

            if (!Split) continue;

            SmallVector<BasicBlock *, 2> NewBBs;
            SplitLandingPadPredecessors(LPad, Parent, ".1", ".2", NewBBs);
        }
    }
}

bool InterFunctionShuffleBlock::runOnModule(Module &M) {
	LLVM_DEBUG(outs() << "InterFunctionShuffleBlock debug!\n");
    // outs() << "InterFunctionShuffleBlock debug!\n";
    // if (M.getName().startswith("source/b") || M.getName().startswith("source/d")
    //     /*|| M.getName().startswith("source/f") || M.getName().startswith("source/l") */)
    //     return false;

    // if (! M.getName().startswith("source/libparest/master/newton_method"))
    //     return false;
    // if (M.getName().startswith("source/libparest/master/m") || M.getName().startswith("source/libparest/master/s") )
    //     return false;
    // if (! M.getName().startswith("source/me-tomography/me_s"))
    //     return false;
    // if (M.getName().startswith("source/me-tomography/s") || M.getName().startswith("source/me-tomography/g")
    //     /*|| M.getName().startswith("source/me-tomography/m") || M.getName().startswith("source/me-tomography/t")*/ )
    //     return false;
    // errs() << "name: " << M.getName() << "\n";
    bool Changed = false;

    LLVMContext &C = M.getContext();
    
    // Get all the functions.
    SmallVector<Function *, 4> Functions;
    // uint index = 0;
    for (Function &F : M) {
        // errs() << F.getName() << "\n";
        // if (F.getName() != "main")
        //     continue;
        // if (F.getName() == "_ZN6dealii11SolverGMRESINS_6VectorIdEEE5solveINS_12SparseMatrixIdEENS_16PreconditionSSORIS6_EEEEvRKT_RS2_RKS2_RKT0_"
        //     || F.getName() == "_ZN6dealii8SolverCGINS_6VectorIdEEE5solveINS_12SparseMatrixIdEENS_16PreconditionSSORIS6_EEEEvRKT_RS2_RKS2_RKT0_"
        //     || F.getName() == "_ZN6dealii11SolverGMRESINS_6VectorIdEEE5solveINS_12SparseMatrixIdEENS_9SparseILUIdEEEEvRKT_RS2_RKS2_RKT0_"
        //     || F.getName() == "_ZNK6dealii14SolverSelectorINS_6VectorIdEEE5solveIN9libparest6Master6Master21SchurComplementMatrixENS_20PreconditionIdentityEEEvRKT_RS2_RKS2_RKT0_"
        //     || F.getName() == "_ZN6dealii14SolverBicgstabINS_6VectorIdEEE5solveIN9libparest6Master6Master21SchurComplementMatrixENS_20PreconditionIdentityEEEvRKT_RS2_RKS2_RKT0_"
        //     || F.getName() == "_ZN6dealii8SolverCGINS_6VectorIdEEE5solveIN9libparest6Master6Master21SchurComplementMatrixENS_20PreconditionIdentityEEEvRKT_RS2_RKS2_RKT0_") {
        //     errs() << F.getName() << "\n";
        //     // F.dump();
        //     // continue;
        // } 
        // else
        //     continue;
        // index++;
        // if (index > 241 || index <= 239)
        //     continue;
        // errs() << F.getName() << "\n";
        splitLandingPadPreds(F);
        Functions.push_back(&F);
        // DebugFunction = &F;
        // F.dump();
    }
    // errs() << "function count: " << index << "\n";

    // Extract each block
    // for (Function* F : Functions) {
    //     if (F->isIntrinsic() || F->isDeclaration()) continue;
    //     std::string FuncName = F->getName().str();
    //     LLVM_DEBUG(outs() << "func: " << FuncName << "\n");
    //     for (auto ib = ++(F->begin()), ie = F->end(); ib != ie; ib++) {
    //         SmallVector<std::string, 4> BBNames;
    //         BasicBlock &BB = *ib;
    //         LLVM_DEBUG(outs() << "\tbb: " << BB.getName().str() << "\n");
    //         BBNames.push_back(BB.getName().str());
    //         BlocksByName.push_back(make_pair(FuncName, BBNames));
    //     }
    // }

    // CodeProt: Extract block region
    SmallSetVector<BasicBlock *, 4> SinkBBCandidateSet;
    SmallSetVector<BasicBlock *, 8> SinkBBAllSet;
    SmallSetVector<BasicBlock *, 4> BBsToOutline;

    for (Function *F : Functions) {
		bool needProtect = inConfigOrRandom(ProtName, M, *F, ProtRatio);

		if (needProtect) {
			LLVM_DEBUG(outs() << "func checked: " << F->getName() << "\n");
            //||skipFunction(F)
            if (F->isIntrinsic() || F->isDeclaration() || F->empty() || F->isCreatedByCodeProt() || F->getName().find("std", 0) != StringRef::npos) continue;
            if (F->getName().find("INS_6VectorIdEEE5solveIN") != StringRef::npos) {
                // function SolverGMRES::solve can not be processed, both fusion or fission
                // errs() << "skip INS_6VectorIdEEE5solveIN\n";
                continue;
            } 
            DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>(*F).getDomTree();
            BlockFrequencyInfo &BFI = getAnalysis<BlockFrequencyInfoWrapperPass>(*F).getBFI();
            std::string FuncName = F->getName().str();
            LLVM_DEBUG(outs() << "Start BBregion Extracting for func: " << FuncName << "\n");
            BasicBlock &EntryBB = F->getEntryBlock();
            SinkBBAllSet.clear();
            SinkBBAllSet.insert(&EntryBB);
            SinkBBCandidateSet.clear();
            SinkBBCandidateSet.insert(&EntryBB);

            // std::vector<uint64_t> blockFreqSet = getBlockFreqVec(*F);
            // uint64_t blockNum = F->getBasicBlockList().size();
            uint64_t entryBBFreq = BFI.getBlockFreq(&EntryBB).getFrequency();

            while (!SinkBBCandidateSet.empty()) {
                BasicBlock *TBB = SinkBBCandidateSet.pop_back_val();
                LLVM_DEBUG(outs() << "Region pred BB: " << TBB->getName() << "\n");
                succ_iterator SI = succ_begin(TBB), SE = succ_end(TBB);
                for (; SI != SE; SI++) {
                    BasicBlock *SuccBB = *SI;
                    if (SuccBB->getSinglePredecessor() == nullptr) continue;
                    BBsToOutline.clear();
                    LLVM_DEBUG(outs() << "Region begin BB: " << SuccBB->getName() << "\n");
                    BBsToOutline.insert(SuccBB);

                    auto SSI = ++df_begin(SuccBB), SSE = df_end(SuccBB);
                    while (SSI != SSE) {
                        BasicBlock *SSuccBB = *SSI;
                        bool DomFlag = DT.dominates(SuccBB, SSuccBB);
                        if (!DomFlag) {
                            if (SinkBBAllSet.insert(SSuccBB))
                                SinkBBCandidateSet.insert(SSuccBB);
                            SSI.skipChildren();
                            continue;
                        }
                        LLVM_DEBUG(outs() << "Region Dominated BB: " << SSuccBB->getName() << "\n");
                        BBsToOutline.insert(SSuccBB);
                        ++SSI;
                    }
                    LLVM_DEBUG(outs() << "Extract for func: " << FuncName << " BBsToOutline: " << BBsToOutline.size() << "\n");
                    if (BBsToOutline.size() == 1) {
                        uint64_t regionBeginBBFreq = BFI.getBlockFreq(BBsToOutline.front()).getFrequency();
                        if (regionBeginBBFreq >= (uint64_t)(entryBBFreq * 0.5)) {
                            errs() << "skipped single 'hot' BB\n";
                            continue;
                        }
                    }
                    BlocksByName.push_back(make_pair(FuncName, BBsToOutline));
                }
            }
            LLVM_DEBUG(outs() << "Finish BBregion Extracting for func: " << FuncName << "\n");
		} else {
			LLVM_DEBUG(outs() << "func nochecked: " << F->getName() << "\n");
		}

    }

    // Get all the blocks specified in the input file.
    unsigned NextGroupIdx = GroupsOfBlocks.size();
    GroupsOfBlocks.resize(NextGroupIdx + BlocksByName.size());
    for (const auto &BInfo : BlocksByName) {
        Function *F = M.getFunction(BInfo.first);
        if (!F)
            report_fatal_error("Invalid function name specified in the input file");
        for (const auto &BBInfo : BInfo.second) {
            auto Res = llvm::find_if(*F, [&](const BasicBlock &BB) {
                return &BB == BBInfo;
            });
            if (Res == F->end())
                report_fatal_error("Invalid block name specified in the input file");
            GroupsOfBlocks[NextGroupIdx].push_back(&*Res);
        }
        ++NextGroupIdx;
    }

    // Extract each group of basic blocks.
    for (auto &BBs : GroupsOfBlocks) {
        SmallVector<BasicBlock *, 32> BlocksToExtractVec;
        bool HasInvoke = false, DirectRecursive = false;
        // errs() << "extracting\n";
        for (BasicBlock *BB : BBs) {
                // errs() << "checking\n";
                // BB->dump();
                // Check if the module contains BB.
                if (BB->getParent()->getParent() != &M)
                    report_fatal_error("Invalid basic block");
                LLVM_DEBUG(outs() << "InterFunctionShuffleBlock: Extracting "
                        << BB->getParent()->getName() << ":" << BB->getName()
                        << "\n");
            for (Instruction &I : *BB) {
                if (const CallInst *CI = dyn_cast<CallInst>(&I)) {
                    if (BB->getParent() == CI->getCalledFunction()) {
                        DirectRecursive = true;
                        // errs() << BB->getParent()->getName() << " DirectRecursive\n";
                    }
                } else if (const CatchPadInst *CPI = dyn_cast<CatchPadInst>(&I)) {
                    HasInvoke = true;
                    errs() << "has CatchPadInst, continue\n";
                    break;
                } else if (const LandingPadInst *LPI = dyn_cast<LandingPadInst>(&I)) {
                    if (LPI->isCleanup() && LPI->getNumClauses() >= 2) {
                        HasInvoke = true;
                        // errs() << "has two catch, continue\n";
                        break;
                    }/* else if (LPI->getNumClauses() >= 1 && LPI->isCatch(0)) {
                        // errs() << "catching\n";
                        if (LPI->getClause(0)->isNullValue()) {
                            errs() << "null\n";
                            HasInvoke = true;
                        }
                        // LPI->getClause(0)->dump();
                        // LPI->getClause(0)->getType()->dump();
                    }*/
                } /*else if (const ResumeInst *RI = dyn_cast<ResumeInst>(&I)) {
                    const Instruction * BeginInst = &*RI->getParent()->begin();
                    if (isa<PHINode>(BeginInst)) {
                        errs() << "found a resume inst\n";
                        HasInvoke = true;
                        break;
                    }
                    
                }*/
            }
            if (HasInvoke) break;
            BlocksToExtractVec.push_back(BB);
            // if (const InvokeInst *II = dyn_cast<InvokeInst>(BB->getTerminator())) {
            //     BlocksToExtractVec.push_back(II->getUnwindDest());
            //     LLVM_DEBUG(outs() << "InterFunctionShuffleBlockII: Extracting "
            //             << BB->getParent()->getName() << ":" << II->getUnwindDest()->getName()
            //             << "\n");
            // }
            ++NumExtracted;
            Changed = true;
        }
        if (HasInvoke) continue;
        uint OriginNameLength = 0;
        if (BlocksToExtractVec.size() > 0)
            OriginNameLength = (*BBs.begin())->getParent()->getName().size();
        Function *ExtractedFunc = CPCodeExtractor(BlocksToExtractVec).extractCodeRegion(DirectRecursive);
        if (ExtractedFunc) {
            LLVM_DEBUG(outs() << "Extracted group '" << (*BBs.begin())->getName()
                    << "' in: " << ExtractedFunc->getName() << '\n');
            ExtractedFunc->setCreatedByCodeProt(true);
            errs() << "cp extracted blocks\n";
            // ExtractedFunc->dump();
            // if (DebugFunction)
            //     DebugFunction->dump();
            // if (ExtractedFunc->arg_size() > 16) {
            //     errs() << "too many args: ";
            //     errs() << ExtractedFunc->arg_size() << "\n";
            // }
            assert(OriginNameLength > 0 && "how can the name of a function is empty?");
            ExtractedFunc->setOriginNameLength(OriginNameLength);
            // appendToUsed(M, ExtractedFunc);
            ExtractedFunc->addFnAttr(Attribute::NoInline);
            if (rand() % 2 == 1)
                FissionFunction.push_back(ExtractedFunc);
        }
        else {
            LLVM_DEBUG(outs() << "Failed to extract for group '"
                << (*BBs.begin())->getName() << "'\n");
        }

    }

    unsigned size = FissionFunction.size();
    vector<Constant*> VTableInitVector;
    for (unsigned i = 0; i < size; i++) {
        Function *Fis = FissionFunction.at(i);
        Constant *Con = ConstantExpr::getBitCast(Fis, Type::getInt8PtrTy(C));
        VTableInitVector.push_back(Con);
    }
    ArrayRef<Constant*> VTableInitRef(VTableInitVector);
    ArrayType *VTableTy = ArrayType::get(Type::getInt8PtrTy(C), size);
    Constant *InitValue = ConstantArray::get(VTableTy, VTableInitRef);
    string FileName = M.getName().str().substr(0, M.getName().str().rfind("."));
    string VTableName = "_ZTV" + to_string(FileName.size()) + FileName;
    GlobalVariable *VTableForFission = new GlobalVariable(M, VTableTy, true, 
        GlobalValue::LinkOnceODRLinkage, InitValue, VTableName, nullptr, GlobalValue::NotThreadLocal);
    VTableForFission->setDSOLocal(true);
    VTableForFission->setAlignment(8);
    return Changed;
}

bool InterFunctionShuffleBlock::skipFunction(Function *F) {
    for (BasicBlock &BB : *F) {
        if (BB.size() < 3) {
            continue;
        }
        for (Instruction &I : BB) {
            if (const ResumeInst *RI = dyn_cast<ResumeInst>(&I)) {
                const Instruction * BeginInst = &*BB.begin();
                const Instruction * SecondInst = &*(++BB.begin());
                if (isa<PHINode>(BeginInst) && isa<PHINode>(SecondInst)) {
                    errs() << "found a resume inst\n";
                    return true;
                }
            }
        }
    }
    return false;
}

INITIALIZE_PASS_BEGIN(InterFunctionShuffleBlock, "intershuffleblock",
                      "InterFunctionShuffleBlock Pass", false, false)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
// INITIALIZE_PASS_DEPENDENCY(BlockFrequencyInfoWrapperPass)
INITIALIZE_PASS_END(InterFunctionShuffleBlock, "intershuffleblock",
                    "InterFunctionShuffleBlock Pass", false, false)
// static RegisterPass<InterFunctionShuffleBlock> X("intershuffleblock", "InterFunctionShuffleBlock Pass");

ModulePass *llvm::createInterFunctionShuffleBlockPass() {
    return new InterFunctionShuffleBlock();
}
