#include "llvm/Transforms/CodeProt/Utils.h"

#define DEBUG_TYPE "prepare"
using namespace llvm;

class InterFunctionDeepFusionPrepare : public LoopPass {
public:
    static char ID; // Pass identification, replacement for typeid
    const int DeepLevel = LevelDeepFusion;
    InterFunctionDeepFusionPrepare();
    void getAnalysisUsage(AnalysisUsage &AU) const override;
    bool runOnLoop(Loop *L, LPPassManager &LPM) override;
    std::set<Function*> const &getFunctionsWithLoop() const;
};