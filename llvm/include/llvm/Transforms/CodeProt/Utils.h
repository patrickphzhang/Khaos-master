#ifndef LLVM_CODEPROT_UTILS_H
#define LLVM_CODEPROT_UTILS_H

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Pass.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/PassRegistry.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/CodeGen/ISDOpcodes.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/InitializePasses.h"
#include "llvm/PassSupport.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/Cloning.h"


#include <vector>
#include <map>
#include <set>
#include <string>
#include <queue>
#include <stack>
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>
#include "json/json.h"
#include <stdio.h>
#include <sstream>
#include <list>

using namespace llvm;
using namespace std;

namespace llvm {
    extern bool HasJsonParsed;
    extern Json::Value JsonObj;
    extern DenseMap<Function*, SetVector<Function*>*> LoopCalleeMap;
    extern std::set<Function*> FunctionsWithLoop;

    //Global variables for IntraShuffle
    extern std::map<MachineBasicBlock*, unsigned int> PayloadMap;
    extern unsigned int GlobalPayloadIndex;
    extern std::string PayloadSectionString;
    extern std::string SMCSectionString;
    extern std::vector<GlobalVariable *> EncryptedGlobalVariables;
    extern std::vector<int> EncryptedGVSize;
    class ModulePass;
    extern ModulePass *createParseJsonPass();
    extern ModulePass *createInterFunctionFusionPass();
    extern Pass *createInterFunctionPreparePass();
    extern Pass *createSplitBasicBlock(bool flag);
    extern Pass *createInterFunctionShuffleLoopPass();
    extern Pass *createInterFunctionShuffleLoopMultiPass();
    extern Pass *createInterFunctionDeepFusionPreparePass();
    extern ModulePass *createInterFunctionShuffleBlockPass();
    extern ModulePass *createInterFunctionShuffleOptPass(); 
    extern ModulePass *createInterFunctionShufflePositionPass();
    extern ModulePass *createParseCOFFPass();
    extern Pass *createBogus ();
	extern Pass *createBogus (bool flag);
    extern Pass *createFlattening();
	extern Pass *createFlattening(bool flag);
    extern Pass *createSubstitution ();
	extern Pass *createSubstitution (bool flag);
}

bool inConfigOrRandom(const string &ProtName, Module &M, Function &F, int RatioLocal);
bool inConfigOrRandom(const string &ProtName, Module &M, GlobalVariable &GV, int RatioLocal);
string funcNameDemangle(string funcName);

void fixStack(Function *f);
std::string readAnnotate(Function *f);
bool toObfuscate(bool flag, Function *f, std::string attribute);


extern cl::opt<int> RatioGlobal;
extern cl::opt<int> RatioInterFunctionFusion;
extern cl::opt<int> LevelDeepFusion;
extern cl::opt<int> RatioObfuscation;
extern cl::opt<int> RatioInterShuffle;
//extern cl::opt<unsigned long long> PayloadKey;

// KHAOS
extern cl::opt<bool> EnableInterFunctionFusion;
extern cl::opt<bool> EnableInterFunctionShufflePass;
extern cl::opt<bool> EnableInterFunctionShuffleOptPass;
extern cl::opt<bool> FissionedFunctionOnly;
extern cl::opt<bool> OriginFunctionOnly;
extern cl::opt<bool> EnableTransformStat;

// O-LLVM
extern cl::opt<bool> EnableCodeObf;
extern cl::opt<bool> EnableCodeObfSub;
extern cl::opt<bool> EnableCodeObfFla;
extern cl::opt<bool> EnableCodeObfBog;


#define PROTNAME_INTERFUSION    "InterFunctionFusion"
#define PROTNAME_OBFUSCATION    "Obfuscation"
#define PROTNAME_INTERSHUFFLE   "InterFunctionShuffle"
#define PROTNAME_INTERSHUFFLEOPT "InterFunctionShuffleOpt"  //added for intershuffle opt
#endif