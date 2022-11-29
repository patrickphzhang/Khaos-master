#include "llvm/Transforms/Khaos/Utils.h"

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