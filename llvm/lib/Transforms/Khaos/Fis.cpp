//===- Fis.cpp ------------------------------------- ---------------===//
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
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/FormatAdapters.h"

#include <string>

#define DEBUG_TYPE "fis"

namespace {
    struct Fis : public ModulePass {
        static char ID;

        Fis() : ModulePass(ID){
            initializeFisPass(*PassRegistry::getPassRegistry());
        }

        bool isBBInLoop(BasicBlock* BB, LoopInfo &LI);
        bool splittingFunction(Function &F);
        SmallSetVector<BasicBlock*, 8> getHotBBSet(Function &F, BlockFrequency &hotThreshold, LoopInfo &LI);
        SmallVector<SmallVector<BasicBlock*, 8>, 8> buildRegionsToExtract_v1(Function &F, BlockFrequencyInfo &BFI, DominatorTree &DT);
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

char Fis::ID = 0;

//return true if BB is inside a Loop;
//otherwise, return false;
bool Fis::isBBInLoop(BasicBlock* BB, LoopInfo &LI)
{
    if (BB && LI.getLoopFor(BB)) return true;
    return false;
}

//if splitting function F succeeded, return true; otherwise, return false;
bool Fis::splittingFunction(Function &F)
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
Fis::getHotBBSet(Function &F, BlockFrequency &hotThreshold, LoopInfo &LI)
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
Fis::buildRegionsToExtract_v1(Function &F, BlockFrequencyInfo &BFI, DominatorTree &DT)
{
    SmallVector<SmallVector<BasicBlock*, 8>, 8> result;  //regions to extract
    SmallSetVector<BasicBlock *, 4> sinkBBCandidateSet;  //region's entryBB
    SmallSetVector<BasicBlock *, 8> sinkBBAllSet;        //all visited BB
    LoopInfo LI{DT};
    BlockFrequency hotBBFreqThresold = (uint64_t)BFI.getEntryFreq();
    SmallSetVector<BasicBlock*, 8> hotBBSet = getHotBBSet(F, hotBBFreqThresold, LI);  //don't extract hotBBs
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

//try to extract a region in a function into a new function.
//if succeeded, return true;
//else, return false;
bool Fis::extractRegion(SmallVector<BasicBlock*, 8> BBsToExtract,
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
    uint ONL = 0;
    if (BBsToExtract.size() > 0)
            ONL = (*BBsToExtract.begin())->getParent()->getName().size();
    Function *ExtractedFunc = KhaosCodeExtractor(BBsToExtract).extractCodeRegion();
    if (!ExtractedFunc)
        return Changed;

    ExtractedFunc->setKhaosFunction(true);
    assert(ONL > 0 && "how can the name of a function is empty?");
    ExtractedFunc->setONL(ONL);
    if (!ExtractedFunc->hasFnAttribute(Attribute::NoInline))
    {
        if (ExtractedFunc->hasFnAttribute(Attribute::AlwaysInline))
            ExtractedFunc->removeFnAttr(Attribute::AlwaysInline);
        ExtractedFunc->addFnAttr(Attribute::NoInline);
    }
    Changed = true;
    return Changed;
}

//try inlining smaller function after all functions in M had been split;
//don't inline fission function.
bool Fis::tryInlineFunction(Function &F)
{
    bool Changed = false;
    SmallSetVector<CallSite, 16> Calls;
    if (F.isDeclaration() || F.hasFnAttribute(Attribute::NoInline) || F.isKhaosFunction() || !isInlineViable(F))
        return Changed;

    for (User *U : F.users())
        if (auto CS = CallSite(U))
          if (CS.getCalledFunction() == &F &&
              CS.getParent()->getParent() != &F)  //don't inline recursive function
            Calls.insert(CS);

    for (CallSite CS : Calls)
    {
        llvm::InlineFunctionInfo IFI;
        Changed |= InlineFunction(CS, IFI);
    }
    return Changed;
}

bool Fis::runOnModule(Module &M) {
    bool Changed = false;
    // outs() << "Fis::runOnModule\n";
    SmallSetVector<Function *, 8> splittedFuncs;
    for (Function &F : M) 
    {
        //skip LLVM Intrinsic functions, function declarations, empty functions,
        //functions created by Khaos, std functions
		if (F.isIntrinsic() || F.isDeclaration() || F.empty() || F.hasOptNone() ||
            F.isKhaosFunction() || F.getName().find("std", 0) != StringRef::npos ||
            F.skipKhaos()) 
            continue;
        // if (F.getName().size() > 8 ) 
        //     continue;
        // if (F.getName().equals("main")) continue;
        // errs() << "splitting " << F.getName() << "\n";
        
        bool splitFlag = splittingFunction(F);
        if (splitFlag)
        {
            splittedFuncs.insert(&F);
        } 
        Changed |= splitFlag;
    }

    for (Function *F : splittedFuncs)
    {
        if (F->getBasicBlockList().size() > 20/*10*/) continue;
        Changed |= tryInlineFunction(*F);
    }
    return Changed;
}

INITIALIZE_PASS_BEGIN(Fis, "fis",
                      "Fis Pass", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopSimplify)
INITIALIZE_PASS_DEPENDENCY(BlockFrequencyInfoWrapperPass)
INITIALIZE_PASS_END(Fis, "fis",
                    "Fis Pass", false, false)

ModulePass *llvm::createFisPass() {
    return new Fis();
}
