#include "llvm/Transforms/Khaos/DeepFusionPrepare.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
namespace llvm {
    std::set<Function*> FunctionsWithLoop;
}

char DeepFusionPrepare::ID = 0;
DeepFusionPrepare::DeepFusionPrepare() : LoopPass(ID) {
    initializeDeepFusionPreparePass(*PassRegistry::getPassRegistry());
}

void DeepFusionPrepare::getAnalysisUsage(AnalysisUsage &AU) const {
    // Legacy analysis pass to compute dominator tree.
    AU.addRequired<DominatorTreeWrapperPass>();
    // Legacy analysis pass to compute loop infomation.  
    AU.addRequired<LoopInfoWrapperPass>();
    // getLoopAnalysisUsage(AU);
    AU.setPreservesAll();
}

bool DeepFusionPrepare::runOnLoop(Loop *L, LPPassManager &LPM) {
    if (L->getNumBlocks() > 0) {
        Function *F = L->getHeader()->getParent();
        assert(F && "A loop is must in a function!");
        FunctionsWithLoop.insert(F);
    }
    return false;
}

INITIALIZE_PASS_BEGIN(DeepFusionPrepare, "DeepFusionPrepare", "DeepFusionPrepare Pass", /*cfgonly=*/true, /*analysis=*/true)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_END(DeepFusionPrepare, "DeepFusionPrepare", "DeepFusionPrepare Pass", /*cfgonly=*/true, /*analysis=*/true)

Pass *llvm::createDeepFusionPreparePass() {
  return new DeepFusionPrepare();
}