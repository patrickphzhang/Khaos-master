#include "llvm/Transforms/Khaos/Utils.h"

cl::opt<int> RatioGlobal("ratio", cl::init(0), cl::Hidden,
		cl::desc("Protect ratio for all types"));
cl::opt<int> RatioFis("ratio-fis", cl::init(0), cl::Hidden,
		cl::desc("Protect ratio for fission"));
cl::opt<bool> EnableFus("enable-fus", cl::init(false), cl::Hidden,
		cl::desc("Enable Fus"));
cl::opt<bool> FissionedFunctionOnly("sep", cl::init(false), cl::Hidden,
		cl::desc("Only Fusion Fissioned Functions"));
cl::opt<bool> OriginFunctionOnly("ori", cl::init(false), cl::Hidden,
		cl::desc("Only Fusion Origin Functions"));
cl::opt<bool> EnableFis("enable-fis",
				cl::desc("Enable Fission Pass"),
				cl::init(false), cl::Hidden);
cl::opt<bool> EnableTransformStat("enable-transform-stat", 
                cl::desc("Pass can write their tansform-statistics into a json file"),
                cl::init(false),
                cl::Hidden);
bool inConfigOrRandom(const string &KhaosName, Module &M, Function &F, int RatioLocal) {
  if (F.isIntrinsic() || F.isDeclaration()) return false;
	if (RatioGlobal) return ((rand() % 100) < RatioGlobal);
	if (RatioLocal) return ((rand() % 100) < RatioLocal);

	return false;
}

bool inConfigOrRandom(const string& KhaosName, Module& M, GlobalVariable& GV, int RatioLocal) {
	
	// Check if it is a const global variable
	if (GV.isDeclaration() || !GV.isConstant() || !GV.hasInitializer()) {
		return false;
	}
    std::string section(GV.getSection());
    
	// Check if it is a llvm spectial variable
    if (GV.getName() == "llvm.used" || GV.getSection() == "llvm.metadata" ||
        GV.hasAvailableExternallyLinkage() ||
        GV.getName() == "llvm.global_ctors"||
        GV.getName() == "llvm.global_dtors") {
		return false;
	}

	if (RatioGlobal) return ((rand() % 100) < RatioGlobal);
    if (RatioLocal)  return ((rand() % 100) < RatioLocal);

    return false;
}