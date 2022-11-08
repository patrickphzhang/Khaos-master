#include "X86.h"
#include "X86InstrBuilder.h"
#include "X86InstrInfo.h"
#include "X86Subtarget.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/CodeProt/Utils.h"
#include <assert.h>

using namespace llvm;

#define DEBUG_TYPE "deep-fusion"

namespace {
class DeepFusionLevel1Pass : public MachineFunctionPass {

public:
  static char ID;
  DeepFusionLevel1Pass() : MachineFunctionPass(ID) {}
  bool runOnMachineFunction(MachineFunction &MF) override;
  StringRef getPassName() const override {
    return DEBUG_TYPE;
  }
};

char DeepFusionLevel1Pass::ID = 0;

bool DeepFusionLevel1Pass::runOnMachineFunction(MachineFunction &MF) {
  // errs() << "DeepFusionLevel1Pass\n";
  Module &M = const_cast<Module &>(*(MF.getFunction().getParent()));
  Function &F = const_cast<Function &>(MF.getFunction());
  // errs() << F.getName() << "\n";
  if (!F.isCreatedByCodeProt() || MF.size() <= 1)
    return false;
  // errs() << F.getName() << "\n";
  StringRef Fusion("Fusion");
  if (!F.getName().endswith(Fusion))
    return false;
  // MF.dump();
  // F.dump();
  MF.RenumberBlocks();
  for (auto &BB : F) {
    if (BB.getName().startswith("deep_trampoline")) {
      // this is a trampoline bb
      StringRef TrampolineBBName = BB.getName();
      // errs() << "found a trampoline bb: " << TrampolineBBName << "\n";
      // BB.dump();
      // it's asm("nop #ToBBName")
      InlineAsm *AsmValue = nullptr;
      for (auto &I : BB) {
        CallInst *NopInst = dyn_cast<CallInst>(&I);
        if (NopInst) {
          AsmValue = dyn_cast<InlineAsm>(NopInst->getCalledValue());
          if (AsmValue) {
            StringRef AsmString = AsmValue->getAsmString();
            
            if (AsmString.startswith("nop #"))
              break;
            else
              errs() << "Is there another inline asm?\n";
          }
        }
      } 
      assert(AsmValue && "deepfusion.trampoline is an asm call");
      auto AsmString = AsmValue->getAsmString();
      // errs() << "AsmString: " << AsmString << "\n";
      std::string ToBBName = AsmString.substr(5);
      // errs() << "ToBBName: " << ToBBName << "\n";
      
      // find the MBB that use this trampoline bb
      MachineBasicBlock *TrampolineMBB = nullptr, *ToMBB = nullptr;
      for (auto ib = MF.begin(), ie = MF.end(); ib != ie; ib++) {
        MachineBasicBlock *CurMBB = &*ib;
        if (CurMBB->getName().equals(TrampolineBBName)) {
          // errs() << "found the trampoline mbb\n";
          assert(!TrampolineMBB && "there can be only one trampoline MBB!\n");
          TrampolineMBB = CurMBB;
        }
        if (CurMBB->getName().equals(ToBBName)) {
          // errs() << "found the To mbb";
          ToMBB = CurMBB;
        }
      }
      if (!ToMBB) {
        // errs() << "ToMBB is deleted\n";
        // we choose a MBB randomly
        // errs() << MF.size() << "\n";
        ToMBB = MF.getBlockNumbered((rand() % (MF.size() - 1)) + 1);
        // errs() << ToMBB << "\n";
        // continue;
      }
      for (auto ib = MF.begin(), ie = MF.end(); ib != ie; ib++) {
        MachineBasicBlock *CurMBB = &*ib;
        for (auto iit = CurMBB->begin(), iie = CurMBB->end(); iit != iie; iit++) {
          MachineInstr *CurMI = &*iit;

          for (uint i = 0; i < CurMI->getNumOperands(); i++) {
              MachineOperand *MO = &CurMI->getOperand(i);
              if (MO->isMBB() && MO->getMBB() == TrampolineMBB) {
                // errs() << "found a reference\n";
                assert(CurMI->isBranch() && "Only branch are using trampoline!\n");
                // ReferenceBBs.push_back()
                // CurMI->dump();
                MO->setMBB(ToMBB);
              }
          }
        }
      }
    }
  }
  // MF.dump();
  return true;
}

} // end of anonymous namespace


INITIALIZE_PASS(DeepFusionLevel1Pass, "DeepFusionLevel1 Pass",
                DEBUG_TYPE,
                false, // is CFG only?
                false  // is analysis?
)


namespace llvm {
FunctionPass *createDeepFusionLevel1Pass() {
  return new DeepFusionLevel1Pass();
}
} // namespace llvm
