#include "X86.h"
#include "X86InstrBuilder.h"
#include "X86InstrInfo.h"
#include "X86Subtarget.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineJumpTableInfo.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Khaos/Utils.h"
#include <assert.h>

using namespace llvm;

namespace {
std::map<MachineBasicBlock *, unsigned int> IdxMap;
unsigned int GHidIdx = 0;
unsigned long long HidK = 0x0;

class B3 {
private:
  unsigned int StartBBID = 0;
  unsigned int Length = 0;
  MachineFunction *Parent;

public:
  B3(unsigned int StartBBID, unsigned int Length,
                   MachineFunction *MF) {
    this->StartBBID = StartBBID;
    this->Length = Length;
    this->Parent = MF;
  }
  unsigned int getStartBBID() { return this->StartBBID; }
  unsigned int getLength() { return this->Length; }
  MachineFunction *getParent() { return this->Parent; }
};

class HidIntra : public MachineFunctionPass {
private:
  const X86InstrInfo *TII;
  std::string SimplifiedName;
  unsigned int FunctionHidIdx = 0;
  unsigned int BBCount = 0;
  std::vector<B3 *> Budgets;

public:
  static char ID;
  HidIntra() : MachineFunctionPass(ID) {}
  void generateBudgets(MachineFunction &MF);
  void fix();
  void fixOnce(MachineBasicBlock *MBB);
  void fixJCC(MachineBasicBlock *MBB, bool FallThroughNeeded);
  void fixJMP(MachineBasicBlock *MBB);
  void fixDefault(MachineBasicBlock *MBB);
  unsigned int getHidIdx(MachineBasicBlock *MBB);
  unsigned int getIndex();
  void hide(MachineBasicBlock *MBB,
                        unsigned int TargetHidIdx);
  std::string replaceAll(std::string &Str, const std::string &OldVale,
                         const std::string &NewVal);
  std::string getLegalName(std::string &Name);
  bool runOnMachineFunction(MachineFunction &MF) override;
};

char HidIntra::ID = 0;

bool HidIntra::runOnMachineFunction(MachineFunction &MF) {
  HidString.clear();
  Function &F = const_cast<Function &>(MF.getFunction());
  if (F.skipKhaos()) 
    return false;
  std::string name = demangle(MF.getName().str());
  StringRef na(name);
  if (EnableStrip && (na.startswith("std::") || na.startswith("void std::")))  
    return false; 
  if (EnableAutoMode && F.isKhaosFunction())
    return false;
  std::string FName = F.getName();
  if (F.isIntrinsic() || F.isDeclaration())
    return false;
  if (F.getName() != "deobfuscate_helper") {
    if (MF.size() < 2) {
      return false;
    }
    SimplifiedName.clear();
    SimplifiedName.append(getLegalName(FName));
    IdxMap.clear();
    Budgets.clear();
    FunctionHidIdx = GHidIdx;
    BBCount = MF.size();
    
    if (F.hasComdat()) {
      //.section  .payload._ZN4Test5printEv, \"awG\", @progbits,
      //_ZN4Test5printEv, comdat \n\t
      HidString.append(".section  .payload.");
      HidString.append(MF.getName());
      HidString.append(", \"awG\", @progbits, ");
      HidString.append(F.getComdat()->getName());
      HidString.append(", comdat \n\t");
    } else {
      //.section  .payload, \"aw\"\n\t
      HidString.append(".section  .payload, \"aw\"\n\t");
    }

    // Label_Payload_Func:\n\t
    HidString.append("Label_Payload_");
    HidString.append(SimplifiedName);
    HidString.append(":\n\t");
    TII = MF.getSubtarget<X86Subtarget>().getInstrInfo();

    MF.RenumberBlocks();
    generateBudgets(MF);
    if (this->Budgets.size() == 1) {
      // no need to shuffle;
      return true;
    }

    fix();
    
    // add paddings, every function's payload is 4*quad aligned
    unsigned int reminder =
        (4 - (GHidIdx - FunctionHidIdx) % 4) % 4;
    for (unsigned int i = 0; i < reminder; i++) {
      unsigned long long Constant;
      HidString.append(".quad ");
      Constant = std::rand() % 0xffffffffffffffff;
      HidString.append(std::to_string(Constant));
      HidString.append("\n\t");
    }
    HidString.append(".previous\n\t");
  }
  return true;
}

} // end of anonymous namespace

void HidIntra::generateBudgets(MachineFunction &MF) {
  bool flag_one = false;
  B3 *CurrentBudget;
  unsigned int BBID = 0, BudgetLength = 0, i = 0;
  for (auto ib = MF.begin(), ie = MF.end(); ib != ie; ib++, i++) {
    MachineBasicBlock *CurMBB = &*ib;
    assert(CurMBB != nullptr && "this cannot be true.\n");
    BudgetLength++;
    if (CurMBB->size() > 0) {
      MachineInstr *LastInstr = &CurMBB->instr_back();
      switch (LastInstr->getOpcode()) {
      case X86::JCC_1:
      case X86::JCC_2:
      case X86::JCC_4:
      case X86::JMP_1:
      case X86::JMP_2:
      case X86::JMP_4:
      case X86::JMP64r:
      case X86::RET:
      case X86::RETL:
      case X86::RETQ:
      case X86::RETW:
      case X86::RETIL:
      case X86::RETIQ:
      case X86::RETIW:
        // allocate a Budget
        if(!flag_one){
          CurrentBudget = new B3(BBID, BudgetLength, &MF);
          this->Budgets.push_back(CurrentBudget);
          // refresh
          BBID = i + 1;
          BudgetLength = 0;
          flag_one = true;
        }
        break;
      }
    }
  }
}

void HidIntra::fix() {
  for (auto &Budget : this->Budgets) {
    MachineBasicBlock *CurMBB = Budget->getParent()->getBlockNumbered(
        Budget->getStartBBID() + Budget->getLength() - 1);
    if (CurMBB->size() == 0) {
      // insert a jmp, dest is next bb
      fixDefault(CurMBB);
    } else {
      MachineInstr *LastInstr = &CurMBB->instr_back();
      switch (LastInstr->getOpcode()) {
      case X86::JCC_1:
      case X86::JCC_2:
      case X86::JCC_4: {
        fixJCC(CurMBB, true);
        break;
      }
      case X86::JMP_1:
      case X86::JMP_2:
      case X86::JMP_4:
        fixJMP(CurMBB);
        break;
      case X86::JMP64r:
        // fixSwitch
        break;
      case X86::RET:
      case X86::RETL:
      case X86::RETQ:
      case X86::RETW:
      case X86::RETIL:
      case X86::RETIQ:
      case X86::RETIW:
        break;
      default: 
        break;
      }
    }
    // only fix the first branch
    break;
  }
}

void HidIntra::fixJCC(MachineBasicBlock *MBB,
                                          bool FallThroughNeeded) {
  MachineInstr *LastInstr = &MBB->back();
  if (FallThroughNeeded) {
    int FallThroughMBBNumber = MBB->getNumber() + 1;
    MachineBasicBlock *FallThroughMBB =
        MBB->getParent()->getBlockNumbered(FallThroughMBBNumber);
    if (FallThroughMBB) {
      // insert a label at the begin of target
      unsigned int FallThroughHidIdx =
          getHidIdx(FallThroughMBB);
      // indirect jump to fall through using inlineasm
      hide(MBB, FallThroughHidIdx);
    }
  }
  //"replace" jcc with a indirect jump
  if (LastInstr->getOperand(0).isMBB()) {
    // get jcc's target
    MachineBasicBlock *TargetMBB = LastInstr->getOperand(0).getMBB();
    unsigned int TargetHidIdx = getHidIdx(TargetMBB);
    // create a new JCCOperandMBB
    MachineFunction *MF = MBB->getParent();
    MachineBasicBlock *JCCOperandMBB = MF->CreateMachineBasicBlock();
    // insert a indirect jmp in the new JCCOperandMBB
    hide(JCCOperandMBB, TargetHidIdx);
    JCCOperandMBB->setNumber(MF->size());
    MF->insert(MF->end(), JCCOperandMBB);
    // replace jcc's operand
    LastInstr->getOperand(0).setMBB(JCCOperandMBB);
  }
}

void HidIntra::fixJMP(MachineBasicBlock *MBB) {
  MachineInstr *LastInstr = &MBB->instr_back();
  if (LastInstr->getOperand(0).isMBB()) {
    MachineBasicBlock *TargetMBB = LastInstr->getOperand(0).getMBB();
    unsigned int TargetHidIdx = getHidIdx(TargetMBB);
    // remove origin jump
    MBB->erase(LastInstr);
    // insert a indirect jump
    hide(MBB, TargetHidIdx);
  }
}

void HidIntra::fixDefault(MachineBasicBlock *MBB) {
  int MaxNumber = BBCount - 1;
  if (MBB->getNumber() >= MaxNumber)
    return;
  int TargetMBBNumber = MBB->getNumber() + 1;
  MachineBasicBlock *TargetMBB =
      MBB->getParent()->getBlockNumbered(TargetMBBNumber);
  if (TargetMBB) {
    // insert a indirect jump
    unsigned int TargetHidIdx = getHidIdx(TargetMBB);
    hide(MBB, TargetHidIdx);
  }
}

unsigned int
HidIntra::getHidIdx(MachineBasicBlock *MBB) {
  if (IdxMap.find(MBB) == IdxMap.end()) {
    unsigned int Index = getIndex();
    MachineBasicBlock *LabelMBB = MBB;
    IdxMap.insert(std::pair<MachineBasicBlock *, unsigned int>(MBB, Index));
    DebugLoc DL;
    // insert a label at the begin of mbb
    // .global Label_x\n\t
    // Label_x:\n\t
    if (LabelMBB->size())
      DL = LabelMBB->front().getDebugLoc();
    std::string LabelStr(".label_");
    LabelStr.append(itostr(Index));
    LabelStr.append(":\n\t");
    const char *Label = strdup(LabelStr.c_str());
    BuildMI(*LabelMBB, LabelMBB->instr_begin(), DL, TII->get(X86::INLINEASM))
        .addExternalSymbol(Label)
        .addImm(1);
    HidString.append(".quad .label_");
    HidString.append(itostr(Index));

    if (HidK) {
      // payload obfuscation
      // Payload key is an unsigned long long, which can split to four child
      // keys | 63 - 48 | 47 - 32 | 31 - 16 | 15 - 0 | Every child key is an
      // unsigned short, which is used to obfuscate a quad The highest bit
      // indicates the quad should plus or minus a random number The lower 15
      // bits is the random number eg. 0x1234, aka, 0001 0010 0011 0100 means
      // -001 0010 0011 0100
      unsigned int KeyIndex = (Index - FunctionHidIdx) % 4;
      unsigned short TheKey = HidK >> (KeyIndex * 16);
      if (TheKey & 0x8000)
        HidString.append("+");
      else
        HidString.append("-");
      HidString.append(itostr(TheKey & 0x7fff));
    }
    HidString.append("\n\t");
  }
  return IdxMap[MBB];
}

// TODO: add a mutex
unsigned int HidIntra::getIndex() {
  return GHidIdx++;
}

void HidIntra::hide(
    MachineBasicBlock *MBB, unsigned int TargetHidIdx) {
  //“jmpq * (Label_Payload_modulename+TargetHidIdx*8)(%rip)\n\t”;
  std::string JMPString("jmpq * (Label_Payload_");

  JMPString.append(SimplifiedName);
  JMPString.append("+");
  JMPString.append(itostr(TargetHidIdx - FunctionHidIdx));
  JMPString.append("*8)(%rip)\n\t");
  const char *JMPASM = strdup(JMPString.c_str());

  DebugLoc DL;
  if (MBB->size())
    DL = MBB->back().getDebugLoc();
  BuildMI(*MBB, MBB->instr_end(), DL, TII->get(X86::INLINEASM))
      .addExternalSymbol(JMPASM)
      .addImm(1);
}

std::string HidIntra::replaceAll(std::string &Str,
                                                 const std::string &OldVale,
                                                 const std::string &NewVal) {
  while (true) {
    std::string::size_type pos(0);
    if ((pos = Str.find(OldVale)) != std::string::npos) {
      Str.replace(pos, OldVale.length(), NewVal);
    } else
      break;
  }
  return Str;
}

std::string HidIntra::getLegalName(std::string &Name) {
  Name = replaceAll(Name, ".", "_");
  Name = replaceAll(Name, "-", "_");
  Name = replaceAll(Name, "$", "_");
  Name = replaceAll(Name, "@", "_");
  Name = replaceAll(Name, "?", "_");
  Name = replaceAll(Name, "\"", "_");
  Name = replaceAll(Name, "<", "_");
  Name = replaceAll(Name, ">", "_");
  return Name;
}

INITIALIZE_PASS(HidIntra, "HidIntra Pass",
                "HidIntra",
                false, // is CFG only?
                false  // is analysis?
)

namespace llvm {
  std::string HidString;
  FunctionPass *createHidIntra() {
    return new HidIntra();
  }
} // namespace llvm
