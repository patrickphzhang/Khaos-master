#include "llvm/Transforms/CodeProt/Utils.h"

#define DEBUG_TYPE "harmness-analysis"

using namespace llvm;

class HarmnessAnalysis : public ModulePass {
public:
    using HarmnessValuesMapTy = llvm::ValueMap<llvm::Value const *, uint8_t>;   
    static char ID; // Pass identification, replacement for typeid
    HarmnessAnalysis() : ModulePass(ID){}
    bool runOnModule(Module &F) override;
    void getAnalysisUsage(llvm::AnalysisUsage &Info) const override;
    HarmnessValuesMapTy const &getHarmnessMap() const;
    bool isFunctionHarmless(Function *F);
    bool isValueHarmless(Value *value);
    bool isValueFromArg(Value *value);
    bool isTypeHarmless(Type *type);
    // Value *getExactValue(Value * value);
private:
    // 0 : this value is harmless
    // 1 : this value contains harmless part, eg. functions contains harmless BB.
    HarmnessValuesMapTy HarmnessMap; 
    SetVector<Value*> DangerCast;
    // arg set
    SetVector<Value*> ArgsRelated;
    SetVector<Value*> ArgsIrrelevant;
    SetVector<Value*> AnalysisingValues;
};