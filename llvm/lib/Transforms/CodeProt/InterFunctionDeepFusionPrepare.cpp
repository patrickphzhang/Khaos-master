#include "llvm/Transforms/CodeProt/InterFunctionDeepFusionPrepare.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
namespace llvm {
    std::set<Function*> FunctionsWithLoop;
}

char InterFunctionDeepFusionPrepare::ID = 0;
InterFunctionDeepFusionPrepare::InterFunctionDeepFusionPrepare() : LoopPass(ID) {
    initializeInterFunctionDeepFusionPreparePass(*PassRegistry::getPassRegistry());
}

void InterFunctionDeepFusionPrepare::getAnalysisUsage(AnalysisUsage &AU) const {
    // Legacy analysis pass to compute dominator tree.
    AU.addRequired<DominatorTreeWrapperPass>();
    // Legacy analysis pass to compute loop infomation.  
    AU.addRequired<LoopInfoWrapperPass>();
    // getLoopAnalysisUsage(AU);
    AU.setPreservesAll();
}

bool InterFunctionDeepFusionPrepare::runOnLoop(Loop *L, LPPassManager &LPM) {
    // errs() << "InterFunctionDeepFusionPrepare::runOnLoop\n";
    if (L->getNumBlocks() > 0) {
        Function *F = L->getHeader()->getParent();
        assert(F && "A loop is must in a function!");
        // errs() << F->getName() << " has loop(s)\n";
        FunctionsWithLoop.insert(F);
    }
    return false;
}

INITIALIZE_PASS_BEGIN(InterFunctionDeepFusionPrepare, "InterFunctionDeepFusionPrepare", "InterFunctionDeepFusionPrepare Pass", /*cfgonly=*/true, /*analysis=*/true)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_END(InterFunctionDeepFusionPrepare, "InterFunctionDeepFusionPrepare", "InterFunctionDeepFusionPrepare Pass", /*cfgonly=*/true, /*analysis=*/true)

Pass *llvm::createInterFunctionDeepFusionPreparePass() {
  return new InterFunctionDeepFusionPrepare();
}
// static RegisterPass<InterFunctionDeepFusionPrepare> 
//     X("InterFunctionDeepFusionPrepare", 
//       "InterFunctionDeepFusionPrepare Pass", true, true);