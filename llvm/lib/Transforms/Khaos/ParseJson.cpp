//===- ParseJson.cpp ------------------------------------- ---------------===//
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

#define DEBUG_TYPE "parsejson"

cl::opt<int> RatioGlobal("ratio", cl::init(0), cl::Hidden,
		cl::desc("Protect ratio for all types"));
cl::opt<int> RatioObfuscation("ratio-obfuscation", cl::init(0), cl::Hidden,
		cl::desc("Protect ratio for obfuscation"));
cl::opt<int> RatioFis("ratio-fis", cl::init(0), cl::Hidden,
		cl::desc("Protect ratio for fission"));
cl::opt<int> LevelDeepFusion("level-deepfusion", cl::init(0), cl::Hidden,
		cl::desc("Deep fusion level"));
cl::opt<bool> EnableSub("enable-sub", cl::init(false), cl::Hidden,
		cl::desc("Enable Substitution"));
cl::opt<bool> EnableFla("enable-fla", cl::init(false), cl::Hidden,
		cl::desc("Enable Flattening"));
cl::opt<bool> EnableBog("enable-bog", cl::init(false), cl::Hidden,
		cl::desc("Enable Bogus"));
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

namespace llvm {
    bool HasJsonParsed = false;
    Json::Value JsonObj;
}

namespace {
    struct ParseJsonPass : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        ParseJsonPass() : ModulePass(ID) {}

        bool runOnModule(Module &M) override;

    };

}

char ParseJsonPass::ID = 0;

bool ParseJsonPass::runOnModule(Module &M) {
        if (HasJsonParsed == false) {
            HasJsonParsed = true;
            srand((int)time(0));
        }
	return true;

}


static RegisterPass<ParseJsonPass> X("parsejson", "ParseJson Pass");

ModulePass *llvm::createParseJsonPass() {
    return new ParseJsonPass();
}

