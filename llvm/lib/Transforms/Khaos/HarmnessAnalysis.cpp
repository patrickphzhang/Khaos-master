//===- HarmnessAnalysis.cpp - Analyze which entities are harmless ----------===//
//
// An iterative pass, waiting every entity is convergenced.
// An instruction is harmless if it uses harmless opcode.
// A basic block is harmless if all its instruction are harmless.
// A function is harmless is harmless if all its basic block are harmless.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Khaos/HarmnessAnalysis.h"

bool HarmnessAnalysis::isFunctionHarmless(Function *F) {
    // simple now, at first I thought malloc is harmless
    // but it seems that malloc's return value can be propagated quite far
    // so I cut off these kind of call
    // we can add analysis later
    if (F->getName().equals("llvm.memcpy.p0i8.p0i8.i64")) {
        return false;
    }
    if (F->getName().equals("extract_ptrval") ||
        F->getName().equals("extract_ctrlbit") ||
        F->getName().equals("extract_ctrlsign") ||
        F->getName().equals("get_random") ||
        // F->getName().equals("malloc") ||
        F->isIntrinsic() ||
        (HarmnessMap.count(F) && HarmnessMap.lookup(F) == 0)) {
        // errs() << F->getName() << " is harmless\n";    
        return true;
    } else return false;
}

bool HarmnessAnalysis::isTypeHarmless(Type *type) {
    if (type->isFloatingPointTy() || type->isX86_MMXTy()
        || type->isIntegerTy()) {
        return true;
    } else return false;
}


bool HarmnessAnalysis::isValueFromArg(Value * value) {
    if (isa<Constant>(value)) return false;
    else if (ArgsRelated.count(value) > 0) return true;
    else if (User *user = dyn_cast<User>(value)){
        AnalysisingValues.insert(value);
        bool valueFromArg = false;
        for (uint i = 0; i < user->getNumOperands(); i++) {
            Value *Opi = user->getOperand(i);
            if (AnalysisingValues.count(Opi)) {
                // this would happen when there is a circle
                continue;
            }
            if (ArgsIrrelevant.count(Opi))
                return false;
            else if (ArgsRelated.count(Opi)) {
                return true;
            }else if (isValueFromArg(Opi)) {
                valueFromArg = true;
                ArgsRelated.insert(Opi);
                ArgsRelated.insert(value);
                break;
            } else {
                ArgsIrrelevant.insert(Opi);
            }
        }
        AnalysisingValues.remove(value);
        return valueFromArg;
    } else {
        return false;
    }
}
bool HarmnessAnalysis::isValueHarmless(Value * value) {
    bool Harmless = false;
    if (DangerCast.count(value))
        return false;
    if (HarmnessMap.count(value)) {
        if (HarmnessMap[value] == 0)
            Harmless = true;
        else
            Harmless = false;
    } else {
        if (Function *F = dyn_cast<Function>(value)) {
            Harmless = isFunctionHarmless(F);
        } else if (isa<ConstantInt>(value)
                    || isa<ConstantFP>(value)
                    || isa<ConstantPointerNull>(value)) {
            // constant is harmless
            Harmless = true;
        } else {
            Harmless = false;
        }
    }
    return Harmless;
}

bool HarmnessAnalysis::runOnModule(Module &M) {
    HarmnessMap.clear();
    // errs() << "HarmnessAnalysis\n";
    // init harmless map
    for (auto &F : M) {
        // if the arg is scalar type, it is harmless
        Argument *Argi;
        Type * ArgiType;
        for (uint i = 0; i < F.arg_size(); i++) {
            Argi = F.getArg(i);
            ArgiType = Argi->getType();
            if (isTypeHarmless(ArgiType)) {
                HarmnessMap[Argi] = 0;
            }
            ArgsRelated.insert(Argi);
        }
        for (auto &BB : F) {
            for (auto &Inst : BB) {
                // allocas / branches are harmless
                if (isa<AllocaInst>(&Inst)
                    || isa<BranchInst>(&Inst))
                    HarmnessMap[&Inst] = 0;
                // ud2 are harmful
                else if (isa<UnreachableInst>(&Inst))
                    HarmnessMap[&Inst] = 1;
            }
        }
    }
    // errs() << "total " << HarmnessMap.size() << " found\n";
    // 0 harmless
    // 123... tbd
    bool StateChanged = true;
    uint LoopCount = 0;
    while(StateChanged && LoopCount < 1000) {
        LoopCount++;
        StateChanged = false;
        for (auto &F : M) {
            if (F.isDeclaration() || F.isIntrinsic()) continue;
            for (auto &BB : F) {
                for (auto &Inst : BB) {
                    if (HarmnessMap.count(&Inst)) {
                        continue;
                    }
                    bool InstHarmless = true;
                    if (CastInst *CI = dyn_cast<CastInst>(&Inst)) {
                        // we only care cast's src
                        InstHarmless = isValueHarmless(Inst.getOperand(0));
                        if (CI->getDestTy()->isPointerTy() || CI->getSrcTy()->isPointerTy()) {
                            DangerCast.insert(CI);
                        }
                    } else if (PHINode *phi = dyn_cast<PHINode>(&Inst)) {
                        // if all src is harmless, then the phi is harmless
                        for (auto &src : phi->incoming_values()) {
                            Value *ivalue = &*src;
                            if (!isValueHarmless(ivalue)) {
                                InstHarmless = false;
                                // errs() << "one of it's incoming calue is not harmless\n";
                                // ivalue->dump();
                                break;
                            }
                        }
                    } else if (CallBase *CB = dyn_cast<CallBase>(&Inst)) {
                        // callee is an extra operand
                        Function * Callee = CB->getCalledFunction();
                        if (Callee) {
                            if (isFunctionHarmless(Callee) && !isValueFromArg(CB)) {
                                // a harmless call means all the args should be constant
                                // at least, it's not computed by arg
                               InstHarmless = true;
                            } else {                                
                                // errs() << "this call is harmful\n";
                                InstHarmless = false;
                            }
                        } else {
                            // errs() << "indirect call is always harmful\n";
                            InstHarmless = false;
                        }
                    } else {
                        uint OperandNum = Inst.getNumOperands();
                        Value * Opi;
                        for (uint i = 0; i < OperandNum; i++) {
                            Opi = Inst.getOperand(i);
                            if (isa<GlobalVariable>(Opi)) {
                                // errs() << "accessing Constant\n";
                                if (LoadInst *LI = dyn_cast<LoadInst>(&Inst)) {
                                    // loading scalar variable is safe
                                    Type *LdType = LI->getType();
                                    if (!isTypeHarmless(LdType)) {
                                        InstHarmless = false;
                                    }
                                } else {
                                    // store is not allowed
                                    // TODO: is call allowed?
                                    InstHarmless = false;
                                }
                            } else {
                                if (!isValueHarmless(Opi)) {
                                    InstHarmless = false;
                                }
                            }
                        }
                    }
                    if (InstHarmless) {
                        HarmnessMap[&Inst] = 0;
                        StateChanged = true;
                    }  
                }
            }
            if (HarmnessMap.count(&F)) continue;
            bool FunctionHarmless = true;
            for (auto &BB : F) {
                if (HarmnessMap.count(&BB)) continue;
                bool BBHarmless = true;
                for (auto &Inst : BB) {
                    if (!HarmnessMap.count(&Inst) || HarmnessMap[&Inst] != 0) {
                        // this instruction is harmful
                        BBHarmless = false;
                    }
                }
                if (BBHarmless) {
                    HarmnessMap[&BB] = 0;
                    StateChanged = true;
                } else {
                    FunctionHarmless = false;
                }
            }
            if (FunctionHarmless) {
                HarmnessMap[&F] = 0;
                // errs() << "found a harmless function: " << F.getName() << "\n";
                StateChanged = true;
            }
        }
    }
    if (LoopCount == 1000) {
        errs() << "Unable to converge\n";
    }

    for (auto &F : M) {
        uint HarmlessBBCount = 0, HarmfulBBCount = 0;
        for (auto &BB : F) {
            if (BB.size() <= 1) {
                // empty or trampoline BB is not considered
                continue;
            }
            bool BBHarmless = true;
            for (auto &Inst : BB) {
                if (!HarmnessMap.count(&Inst) || HarmnessMap[&Inst] != 0) {
                    // this instruction is harmful
                    BBHarmless = false;
                }
            }
            if (BBHarmless) {
                HarmnessMap[&BB] = 0;
                HarmlessBBCount++;
            } else {
                HarmfulBBCount++;
            }
        }
        if (HarmlessBBCount) {
            if (HarmfulBBCount) {
                HarmnessMap[&F] = 1;
            } else {
                HarmnessMap[&F] = 0;
            }
        }
    }
    return false;
}

void HarmnessAnalysis::getAnalysisUsage(AnalysisUsage &Info) const {
    Info.setPreservesAll();
}

HarmnessAnalysis::HarmnessValuesMapTy const &HarmnessAnalysis::getHarmnessMap() const {
    return HarmnessMap;
}

char HarmnessAnalysis::ID = 0;
static RegisterPass<HarmnessAnalysis>
    X("harmness-analysis",         // pass option
      "analyze harmness entities", // pass description
      true, // does not modify the CFG
      true  // and it's an analysis
      );