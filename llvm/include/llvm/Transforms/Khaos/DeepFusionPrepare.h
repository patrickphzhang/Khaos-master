#include "llvm/Transforms/Khaos/Utils.h"

using namespace llvm;

class DeepFusionPrepare : public LoopPass {
public:
    static char ID; // Pass identification, replacement for typeid
    const int DeepLevel = LevelDeepFusion;
    DeepFusionPrepare();
    void getAnalysisUsage(AnalysisUsage &AU) const override;
    bool runOnLoop(Loop *L, LPPassManager &LPM) override;
    std::set<Function*> const &getFunctionsWithLoop() const;
};