#include "llvm/Transforms/CodeProt/Utils.h"

bool inConfigOrRandom(const string &ProtName, Module &M, Function &F, int RatioLocal) {
    if (F.isIntrinsic() || F.isDeclaration()) return false;
	if (JsonObj.isMember(ProtName)) {
		string moduleName = M.getName().str();
		string funcName = F.getName().str();
		//string funcNameDemangled = funcNameDemangle(funcName);
		string funcNameDemangled = demangle(funcName);
		
		string lineno;
		BasicBlock &firstBB = F.front();
		for (auto ib = firstBB.begin(), ie = firstBB.end(); ib != ie; ib++) {
			DebugLoc DL = (*ib).getDebugLoc();
			if (DL.get()) {
				lineno = to_string(DL.getFnDebugLoc().getLine());
				break;
			}
		}

		for (unsigned int i = 0; i < JsonObj[ProtName].size(); i++) {
			if (JsonObj[ProtName][i]["file"].asString() == moduleName &&
				// JsonObj[ProtName][i]["line"].asString() == lineno &&
				strstr(funcNameDemangled.c_str(), JsonObj[ProtName][i]["func"].asCString())) {
				return true;
			}
		}

	}

	if (RatioGlobal) return ((rand() % 100) < RatioGlobal);
	if (RatioLocal) return ((rand() % 100) < RatioLocal);

	return false;
}

bool inConfigOrRandom(const string& ProtName, Module& M, GlobalVariable& GV, int RatioLocal) {
	
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

	if (JsonObj.isMember(ProtName)) {
      string moduleName = M.getName().str();
      string GVName = GV.getName().str();
      //string GVNameDemangled = funcNameDemangle(GVName);
	  string GVNameDemangled = demangle(GVName);
      for (unsigned int i = 0; i < JsonObj[ProtName].size(); i++) {
        if (JsonObj[ProtName][i]["file"].asString() == moduleName &&
            JsonObj[ProtName][i]["var"].asString() == GVNameDemangled) {
          return true;
        }
      }
    }

	if (RatioGlobal) return ((rand() % 100) < RatioGlobal);
    if (RatioLocal)  return ((rand() % 100) < RatioLocal);

    return false;
}

string funcNameDemangle(string funcName) {
	ItaniumPartialDemangler ipd;
	string funcNameDemangled;
	size_t size = 256;
	char *buf = new char[size];
	if (!ipd.partialDemangle(funcName.c_str())) {
		ipd.getFunctionBaseName(buf, &size);
		funcNameDemangled = buf;
	}
	else {
		funcNameDemangled = funcName;
	}
	delete[] buf;
	return funcNameDemangled;
}

// Shamefully borrowed from ../Scalar/RegToMem.cpp :(
bool valueEscapes(Instruction *Inst) {
  BasicBlock *BB = Inst->getParent();
  for (Value::use_iterator UI = Inst->use_begin(), E = Inst->use_end(); UI != E;
       ++UI) {
    Instruction *I = cast<Instruction>(*UI);
    if (I->getParent() != BB || isa<PHINode>(I)) {
      return true;
    }
  }
  return false;
}

void fixStack(Function *f) {
  // Try to remove phi node and demote reg to stack
  std::vector<PHINode *> tmpPhi;
  std::vector<Instruction *> tmpReg;
  BasicBlock *bbEntry = &*f->begin();

  do {
    tmpPhi.clear();
    tmpReg.clear();

    for (Function::iterator i = f->begin(); i != f->end(); ++i) {

      for (BasicBlock::iterator j = i->begin(); j != i->end(); ++j) {

        if (isa<PHINode>(j)) {
          PHINode *phi = cast<PHINode>(j);
          tmpPhi.push_back(phi);
          continue;
        }
        if (!(isa<AllocaInst>(j) && j->getParent() == bbEntry) &&
            (valueEscapes(&*j) || j->isUsedOutsideOfBlock(&*i))) {
          tmpReg.push_back(&*j);
          continue;
        }
      }
    }
    for (unsigned int i = 0; i != tmpReg.size(); ++i) {
      DemoteRegToStack(*tmpReg.at(i), f->begin()->getTerminator());
    }

    for (unsigned int i = 0; i != tmpPhi.size(); ++i) {
      DemotePHIToStack(tmpPhi.at(i), f->begin()->getTerminator());
    }

  } while (tmpReg.size() != 0 || tmpPhi.size() != 0);
}

std::string readAnnotate(Function *f) {
  std::string annotation = "";

  // Get annotation variable
  GlobalVariable *glob =
      f->getParent()->getGlobalVariable("llvm.global.annotations");

  if (glob != NULL) {
    // Get the array
    if (ConstantArray *ca = dyn_cast<ConstantArray>(glob->getInitializer())) {
      for (unsigned i = 0; i < ca->getNumOperands(); ++i) {
        // Get the struct
        if (ConstantStruct *structAn =
                dyn_cast<ConstantStruct>(ca->getOperand(i))) {
          if (ConstantExpr *expr =
                  dyn_cast<ConstantExpr>(structAn->getOperand(0))) {
            // If it's a bitcast we can check if the annotation is concerning
            // the current function
            if (expr->getOpcode() == Instruction::BitCast &&
                expr->getOperand(0) == f) {
              ConstantExpr *note = cast<ConstantExpr>(structAn->getOperand(1));
              // If it's a GetElementPtr, that means we found the variable
              // containing the annotations
              if (note->getOpcode() == Instruction::GetElementPtr) {
                if (GlobalVariable *annoteStr =
                        dyn_cast<GlobalVariable>(note->getOperand(0))) {
                  if (ConstantDataSequential *data =
                          dyn_cast<ConstantDataSequential>(
                              annoteStr->getInitializer())) {
                    if (data->isString()) {
                      annotation += data->getAsString().lower() + " ";
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  return annotation;
}

bool toObfuscate(bool flag, Function *f, std::string attribute) {
  std::string attr = attribute;
  std::string attrNo = "no" + attr;

  // Check if declaration
  if (f->isDeclaration()) {
    return false;
  }

  // Check external linkage
  if(f->hasAvailableExternallyLinkage() != 0) {
    return false;
  }

  // We have to check the nofla flag first
  // Because .find("fla") is true for a string like "fla" or
  // "nofla"
  if (readAnnotate(f).find(attrNo) != std::string::npos) {
    return false;
  }

  // If fla annotations
  if (readAnnotate(f).find(attr) != std::string::npos) {
    return true;
  }

  // If fla flag is set
  if (flag == true) {
    /* Check if the number of applications is correct
    if (!((Percentage > 0) && (Percentage <= 100))) {
      LLVMContext &ctx = llvm::getGlobalContext();
      ctx.emitError(Twine("Flattening application function\
              percentage -perFLA=x must be 0 < x <= 100"));
    }
    // Check name
    else if (func.size() != 0 && func.find(f->getName()) != std::string::npos) {
      return true;
    }

    if ((((int)llvm::cryptoutils->get_range(100))) < Percentage) {
      return true;
    }
    */
    return true;
  }

  return false;
}