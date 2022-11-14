//===- InterFunctionShuffleOpt.cpp ------------------------------------- ---------------===//
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
#include "llvm/Transforms/Khaos/KhaosCodeExtractor.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
//#include "llvm/Analysis/BlockFrequencyInfoImpl.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/FormatAdapters.h"

#include <string>

#define DEBUG_TYPE "intershuffleopt"

static cl::opt<bool> InlineSplittedFunction("inline-splitted-func", cl::init(false), cl::Hidden,
		cl::desc("Inline Function After Splitted"));

STATISTIC(NumBlocksExtracted, "Number of basic blocks extracted by InterFunctionShuffleOpt");
STATISTIC(NumTotalBlocks, "Number of module's block");
STATISTIC(NumExtractRegionFailed, "Number of extracting region failed by InterFunctionShuffleOpt");
STATISTIC(NumExtractRegionSucceeded, "Number of extracting region succeeded by InterFunctionShuffleOpt");
STATISTIC(NumSkippedFunction, "Number of function skipped");
STATISTIC(NumSplittedFunction, "Number of function splitted");
STATISTIC(NumInlinedFunction, "Number of function inlined");
STATISTIC(NumCallSiteEliminated, "Number of callsite eliminated");

namespace {
    struct InterFunctionShuffleOpt : public ModulePass {
        static char ID;
        const string ProtName = PROTNAME_INTERSHUFFLEOPT;
        const int ProtRatio = RatioInterShuffle;
        Json::Value root;  //record transform statistics in this json value

        InterFunctionShuffleOpt() : ModulePass(ID){
            initializeInterFunctionShuffleOptPass(*PassRegistry::getPassRegistry());
        }

        bool isBBInLoop(BasicBlock* BB, LoopInfo &LI);
        bool splittingFunction(Function &F);
        SmallSetVector<BasicBlock*, 8> getHotBBSet(Function &F, BlockFrequency &hotThreshold, LoopInfo &LI);
        SmallVector<SmallVector<BasicBlock*, 8>, 8> buildRegionsToExtract_v1(Function &F, BlockFrequencyInfo &BFI, DominatorTree &DT);
        SmallVector<SmallVector<BasicBlock*, 8>, 8> buildRegionsToExtract_v2(Function &F, BlockFrequencyInfo &BFI, DominatorTree &DT);
        void printBBFreqency(Function &F);
        bool extractRegion(SmallVector<BasicBlock*, 8> BBsToExtract,
                           DominatorTree *DT, bool AggregateArgs, BlockFrequencyInfo *BFI,
                           BranchProbabilityInfo *BPI, AssumptionCache *AC,
                           bool AllowVarArgs, bool AllowAlloca);
        bool tryInlineFunction(Function &F);

        bool runOnModule(Module &M) override;

        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.addRequiredID(LoopSimplifyID);
            AU.addRequired<BlockFrequencyInfoWrapperPass>();
        }
    };
} // end anonymous namespace

char InterFunctionShuffleOpt::ID = 0;

//return true if BB is inside a Loop;
//otherwise, return false;
bool InterFunctionShuffleOpt::isBBInLoop(BasicBlock* BB, LoopInfo &LI)
{
    if (!BB) return false;
    llvm::Loop* loop = LI.getLoopFor(BB);
    if (!loop/* || LI.isLoopHeader(BB)*/) return false;
    return true;
}

//if splitting function F succeeded, return true; otherwise, return false;
bool InterFunctionShuffleOpt::splittingFunction(Function &F)
{
    bool changed = false;
    BlockFrequencyInfo& BFI= getAnalysis<BlockFrequencyInfoWrapperPass>(F).getBFI();
    BranchProbabilityInfo& BPI = getAnalysis<BranchProbabilityInfoWrapperPass>(F).getBPI();
    DominatorTree DT(F);
    SmallVector<SmallVector<BasicBlock*, 8>, 8> regions2Extract;
    regions2Extract = buildRegionsToExtract_v1(F, BFI, DT);

    for (auto region : regions2Extract)
    {
        changed |= extractRegion(region, &DT, true, &BFI, &BPI, nullptr, true, true);
    }
    return changed;
}

//BB is considered as hotBB if its blockfrequency is greater than hotThreshold.
SmallSetVector<BasicBlock*, 8> 
InterFunctionShuffleOpt::getHotBBSet(Function &F, BlockFrequency &hotThreshold, LoopInfo &LI)
{
    SmallSetVector<BasicBlock*, 8> hotBBSet;
    BlockFrequencyInfo& BFI= getAnalysis<BlockFrequencyInfoWrapperPass>(F).getBFI();
    for (BasicBlock &BB : F)
    {
        //don't consider BB in loop as hot BB
        if (BFI.getBlockFreq(&BB) < hotThreshold ||
            isBBInLoop(&BB, LI) ||                          //BB in loop is cold, to extract the whole loop
            isa<SwitchInst>(BB.getTerminator()))            //BB in switch is cold, to extract the whole switch-case
            continue;
        hotBBSet.insert(&BB);
    }
    return hotBBSet;
}

SmallVector<SmallVector<BasicBlock*, 8>, 8>
InterFunctionShuffleOpt::buildRegionsToExtract_v1(Function &F, BlockFrequencyInfo &BFI, DominatorTree &DT)
{
    SmallVector<SmallVector<BasicBlock*, 8>, 8> result;  //regions to extract
    SmallSetVector<BasicBlock *, 4> sinkBBCandidateSet;  //region's entryBB
    SmallSetVector<BasicBlock *, 8> sinkBBAllSet;        //all visited BB
    LoopInfo LI{DT};
    BlockFrequency hotBBFreqThresold = (uint64_t)BFI.getEntryFreq();
    SmallSetVector<BasicBlock*, 8> hotBBSet = getHotBBSet(F, hotBBFreqThresold, LI);  //don't extract hotBBs
    //std::string FuncName = F.getName().str();
    BasicBlock &EntryBB = F.getEntryBlock();
    
    //EntryBB is considered as hotBB.
    sinkBBAllSet.clear();
    sinkBBAllSet.insert(&EntryBB);
    sinkBBCandidateSet.clear();
    succ_iterator SI = succ_begin(&EntryBB), SE = succ_end(&EntryBB);
    for (; SI != SE; SI++) {
        if (sinkBBAllSet.insert(*SI))
            sinkBBCandidateSet.insert(*SI);
    }

    while (!sinkBBCandidateSet.empty()) {
        BasicBlock *BB = sinkBBCandidateSet.pop_back_val();
        if (hotBBSet.count(BB))
        {
            succ_iterator SI = succ_begin(BB), SE = succ_end(BB);
            for (; SI != SE; SI++) {
                if (sinkBBAllSet.insert(*SI))
                    sinkBBCandidateSet.insert(*SI);
            }
            continue;
        }
        BasicBlock *regionEntryBB = BB;
        SmallSetVector<BasicBlock *, 8> regionBBs;
        LLVM_DEBUG(outs() << "Region entryBB: " << regionEntryBB->getName() << "\n");
        regionBBs.insert(regionEntryBB);
        auto SSI = ++df_begin(regionEntryBB), SSE = df_end(regionEntryBB);
        while (SSI != SSE) {
            BasicBlock *SuccBB = *SSI;
            bool DomFlag = DT.dominates(regionEntryBB, SuccBB);
            if (!DomFlag) {
                if (sinkBBAllSet.insert(SuccBB))
                    sinkBBCandidateSet.insert(SuccBB);
                SSI.skipChildren();
                continue;
            }
            LLVM_DEBUG(outs() << "Region Dominated BB: " << SuccBB->getName() << "\n");
            regionBBs.insert(SuccBB);
            ++SSI;
        }
        // check for exception handling
        bool Splittable = true;
        for (auto &BB : regionBBs) {
            for (auto &I : *BB) {
                if (const LandingPadInst *LPI = dyn_cast<LandingPadInst>(&I)) {
                    if (LPI->isCleanup() && LPI->getNumClauses() >= 2) {
                        Splittable = false;
                        errs() << "two catches\n";
                        // two catches are much complicated than one, we do not split them for now;
                    }
                }
            }
        }
        if (!Splittable)
            continue;
        SmallVector<BasicBlock *, 8> tmp(regionBBs.begin(), regionBBs.end());
        result.push_back(tmp);
    }
    return result;
}

/*划分区域需要考虑的因素： 
 *  1. 支配关系: 不支配的节点加入regionBeginBB集合
 *  2. hotBB  : hotBB的后继加入regionBeginBB集合
 */
SmallVector<SmallVector<BasicBlock*, 8>, 8>
InterFunctionShuffleOpt::buildRegionsToExtract_v2(Function &F, BlockFrequencyInfo &BFI, DominatorTree &DT)
{
    SmallVector<SmallVector<BasicBlock*, 8>, 8> result;    //regions to extract
    SmallSetVector<BasicBlock *, 4> regionPredBBSet;       //region's PredBB
    SmallSetVector<BasicBlock *, 32> visitedBBSet;         //all visited BB
    BlockFrequency hotBBFreqThresold = (uint64_t)BFI.getEntryFreq() * 0.5;
    LoopInfo LI{DT};
    SmallSetVector<BasicBlock*, 8> hotBBSet;               //don't extract hotBBs
    hotBBSet = getHotBBSet(F, hotBBFreqThresold, LI);
    std::string FuncName = F.getName().str();
    BasicBlock &EntryBB = F.getEntryBlock();
    
    
    regionPredBBSet.insert(&EntryBB);
    visitedBBSet.insert(&EntryBB);
    while (!regionPredBBSet.empty()) {
        BasicBlock *predBB = regionPredBBSet.pop_back_val();
        succ_iterator SI = succ_begin(predBB), SE = succ_end(predBB);
        for (; SI != SE; SI++) {
            if (!visitedBBSet.insert(*SI)) continue;
            if (hotBBSet.count(*SI))
            {
                regionPredBBSet.insert(*SI);
                continue;
            }
            SmallSetVector<BasicBlock *, 8> regionBBs;
            BasicBlock *regionEntryBB = *SI;
            LLVM_DEBUG(outs() << "Region entryBB: " << regionEntryBB->getName() << "\n");
            regionBBs.insert(regionEntryBB);
            auto SSI = ++df_begin(regionEntryBB), SSE = df_end(regionEntryBB);
            while (SSI != SSE) {
                BasicBlock *SuccBB = *SSI;
                bool DomFlag = DT.dominates(regionEntryBB, SuccBB);
                if (!DomFlag) {
                    regionPredBBSet.insert(*pred_begin(SuccBB));
                    SSI.skipChildren();
                    continue;
                }
                visitedBBSet.insert(SuccBB);
                LLVM_DEBUG(outs() << "Region Dominated BB: " << SuccBB->getName() << "\n");
                regionBBs.insert(SuccBB);
                ++SSI;
            }
            SmallVector<BasicBlock *, 8> tmp(regionBBs.begin(), regionBBs.end());
            result.push_back(tmp);
        }
    }
    return result;
}

//print frequency of BBs in function F
void InterFunctionShuffleOpt::printBBFreqency(Function &F)
{
    BlockFrequencyInfo& BFI= getAnalysis<BlockFrequencyInfoWrapperPass>(F).getBFI();
    outs() << "-------------Block Frequency list( " << F.getName() << "  "
           << F.getBasicBlockList().size() << " BBs)-------------\n";
    std::string S;
    for (BasicBlock &BB : F)
    {
        S = llvm::formatv("\t\t{0}\t{1}\n",
                           fmt_align(BFI.getBlockFreq(&BB).getFrequency(), AlignStyle::Left, 15),
                           BB.getName());
        outs() << S;                           
    }
    outs() << "\n";
}

//try to extract a region in a function into a new function.
//if succeeded, return true;
//else, return false;
bool InterFunctionShuffleOpt::extractRegion(SmallVector<BasicBlock*, 8> BBsToExtract,
                                            DominatorTree *DT, bool AggregateArgs, BlockFrequencyInfo *BFI,
                                            BranchProbabilityInfo *BPI, AssumptionCache *AC,
                                            bool AllowVarArgs, bool AllowAlloca)
{
    bool Changed = false;
    if (BBsToExtract.size() <= 0) return Changed;
    StringRef oldFunctionName = BBsToExtract[0]->getParent()->getName();
    SmallVector<StringRef, 32> Block2ExtractNameVec;
    SmallDenseMap<StringRef, SmallSetVector<uint, 8>> BBName2LineNoMap;
    // bool DirectRecursive = false;
    if (EnableTransformStat)
    {
        for (BasicBlock *BB : BBsToExtract)
        {
            Block2ExtractNameVec.push_back(BB->getName());
            SmallSetVector<uint, 8> lineNoSetToExtract;
            for (Instruction& I : *BB)
            {
                // if (const CallInst *CI = dyn_cast<CallInst>(&I)) {
                //     if (BB->getParent() == CI->getCalledFunction()) {
                //         DirectRecursive = true;
                //         errs() << BB->getParent()->getName() << " DirectRecursive\n";
                //     }
                // }
                if (I.getDebugLoc())
                {
                    const DebugLoc &DL = I.getDebugLoc();
                    unsigned int line = DL.getLine();
                    //unsigned int column = DL.getCol();
                    if (line > 0) lineNoSetToExtract.insert(line);
                }

            }
            BBName2LineNoMap.insert(make_pair(BB->getName(), lineNoSetToExtract));
        }
    }
    uint OriginNameLength = 0;
    if (BBsToExtract.size() > 0)
            OriginNameLength = (*BBsToExtract.begin())->getParent()->getName().size();
    Function *ExtractedFunc = KhaosCodeExtractor(BBsToExtract).extractCodeRegion();
    if (!ExtractedFunc)
    {
        LLVM_DEBUG(outs() << "Failed to extract for group '"
            << (*BBsToExtract.begin())->getName() << "'\n");
        NumExtractRegionFailed++;
        return Changed;
    }

    LLVM_DEBUG(outs() << "Extracted group '" << (*BBsToExtract.begin())->getName()
                      << "' in: " << ExtractedFunc->getName() << '\n');
    ExtractedFunc->setCreatedByKhaos(true);
    assert(OriginNameLength > 0 && "how can the name of a function is empty?");
    ExtractedFunc->setOriginNameLength(OriginNameLength);
    if (!ExtractedFunc->hasFnAttribute(Attribute::NoInline))
    {
        if (ExtractedFunc->hasFnAttribute(Attribute::AlwaysInline))
        {
            ExtractedFunc->removeFnAttr(Attribute::AlwaysInline);
        }
        ExtractedFunc->addFnAttr(Attribute::NoInline);
    }
    NumBlocksExtracted += BBsToExtract.size();
    NumExtractRegionSucceeded++;
    Changed = true;
    errs() << "STATISTICS Extracted: " << oldFunctionName << " to " << ExtractedFunc->getName() << " size: " << ExtractedFunc->size() << "\n";
    // if (oldFunctionName.startswith("Queue")) {
    // ExtractedFunc->dump();
    // }
    if (EnableTransformStat)  //enable transform statistics for pass
    {
        StringRef newFuncName = ExtractedFunc->getName(); 
        for (StringRef &bbName : Block2ExtractNameVec)
        {
            if (BBName2LineNoMap.find(bbName) != BBName2LineNoMap.end())
            {
                //with -g option, record BB name and line number.
                for (uint lineNo : BBName2LineNoMap[bbName])
                    //root[ProtName][oldFunctionName.str()][newFuncName.str()].append(bbName.str());
                    root[ProtName][oldFunctionName.str()][newFuncName.str()][bbName.str()].append(lineNo);
            }
            else
            {
                //without -g option, record BB name.
                root[ProtName][oldFunctionName.str()][newFuncName.str()].append(bbName.str());
            }
        }
            
    }
    return Changed;
}

//try inlining smaller function after all functions in M had been split;
//don't inline fission function.
bool InterFunctionShuffleOpt::tryInlineFunction(Function &F)
{
    bool Changed = false;
    SmallSetVector<CallSite, 16> Calls;
    if (F.isDeclaration() || F.hasFnAttribute(Attribute::NoInline) || F.isCreatedByKhaos() || !isInlineViable(F))
    {
        return Changed;
    }

    for (User *U : F.users())
        if (auto CS = CallSite(U))
          if (CS.getCalledFunction() == &F &&
              CS.getParent()->getParent() != &F)  //don't inline recursive function
            Calls.insert(CS);

    for (CallSite CS : Calls)
    {
        llvm::InlineFunctionInfo IFI;
        bool inlineFlag = InlineFunction(CS, IFI);
        if (inlineFlag) NumCallSiteEliminated++;
        Changed |= inlineFlag;
    }
    return Changed;
}

bool InterFunctionShuffleOpt::runOnModule(Module &M) {
    bool Changed = false;
    
    SmallSetVector<Function *, 8> splittedFuncs;
    // errs() << "Module Name: " << M.getName() << "\n";
    for (Function &F : M) 
    {
        //skip LLVM Intrinsic functions, function declarations, empty functions,
        //functions created by Khaos, std functions
		if (F.isIntrinsic() || F.isDeclaration() || F.empty() || F.hasOptNone() ||
            F.isCreatedByKhaos() || F.getName().find("std", 0) != StringRef::npos ||
            F.getName().find("INS_6VectorIdEEE5solveIN") != StringRef::npos) 
            continue;
        
        bool needProtect = inConfigOrRandom(ProtName, M, F, ProtRatio);
        if (!needProtect) { 
			//LLVM_DEBUG(outs() << "InterShuffle skipped function: " << F.getName() << "\n");
            continue;
        }
        LLVM_DEBUG(printBBFreqency(F));
        LLVM_DEBUG(outs() << "InterShuffle try to split function: " << F.getName() << "\n");
        errs() << "STATISTICS Funtion origin info: " << F.getName() << ", " << F.size() << "\n";
        
        // outs() << "InterShuffle try to split function: " << F.getName() << "\n";
        // F.dump();
        bool splitFlag = splittingFunction(F);
        if (splitFlag)
        {
            splittedFuncs.insert(&F);
            NumSplittedFunction++;
        } 
        errs() << "STATISTICS After splitting info: " << F.getName() << ", " << F.size() << "\n";
        // if (F.getName().startswith("Queue")) {
        // F.dump();
        // }
        Changed |= splitFlag;
    }

    if (InlineSplittedFunction)
    {
        for (Function *F : splittedFuncs)
        {
            if (F->getBasicBlockList().size() > 20/*10*/) continue;
            bool inlineFlag = tryInlineFunction(*F);
            if (inlineFlag)
            {
                NumInlinedFunction++;
            }
            Changed |= inlineFlag;
        }
    }

    if (EnableTransformStat)
    {
        ofstream fd;
        //StringRef prefixName = M.getName().rsplit('.').first;
        StringRef suffixName("_trans_stat.json");  //transform statistics
        Twine fileName = M.getName() + suffixName;
        fd.open(fileName.str(), ios::out/* | ios::app*/);
        Json::StyledWriter writer;
        fd << writer.write(root);
        fd.flush();
        fd.close();
    }

    return Changed;
}

INITIALIZE_PASS_BEGIN(InterFunctionShuffleOpt, "intershuffleopt",
                      "InterFunctionShuffleOpt Pass", false, false)
//INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopSimplify)
INITIALIZE_PASS_DEPENDENCY(BlockFrequencyInfoWrapperPass)
INITIALIZE_PASS_END(InterFunctionShuffleOpt, "intershuffleopt",
                    "InterFunctionShuffleOpt Pass", false, false)
// static RegisterPass<InterFunctionShuffleOpt> X("intershuffleopt", "InterFunctionShuffleOpt Pass");

ModulePass *llvm::createInterFunctionShuffleOptPass() {
    return new InterFunctionShuffleOpt();
}
