//===- Substitution.cpp ------------------------------------- ---------------===//
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

#include "llvm/Transforms/CodeProt/Utils.h"
#include "llvm/CryptoUtils.h"

#define DEBUG_TYPE "substitution"

#define NUMBER_ADD_SUBST 4
#define NUMBER_SUB_SUBST 3
#define NUMBER_AND_SUBST 2
#define NUMBER_OR_SUBST 2
#define NUMBER_XOR_SUBST 2

static cl::opt<int>
ObfTimes("sub_loop",
         cl::desc("Choose how many time the -sub pass loops on a function"),
         cl::value_desc("number of times"), cl::init(1), cl::Optional);


// Stats
STATISTIC(Add, "Add substitued");
STATISTIC(Sub, "Sub substitued");
// STATISTIC(Mul,  "Mul substitued");
// STATISTIC(Div,  "Div substitued");
// STATISTIC(Rem,  "Rem substitued");
// STATISTIC(Shi,  "Shift substitued");
STATISTIC(And, "And substitued");
STATISTIC(Or, "Or substitued");
STATISTIC(Xor, "Xor substitued");

namespace {
    struct Substitution : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        const string ProtName = PROTNAME_OBFUSCATION;
        const int ProtRatio = RatioObfuscation;
        
        bool runOnModule(Module &M) override;

        bool (Substitution::*funcAdd[NUMBER_ADD_SUBST])(BinaryOperator *bo);
        bool (Substitution::*funcSub[NUMBER_SUB_SUBST])(BinaryOperator *bo);
        void (Substitution::*funcAnd[NUMBER_AND_SUBST])(BinaryOperator *bo);
        void (Substitution::*funcOr[NUMBER_OR_SUBST])(BinaryOperator *bo);
        void (Substitution::*funcXor[NUMBER_XOR_SUBST])(BinaryOperator *bo);
        bool flag;

        Substitution() : ModulePass(ID) {}

        Substitution(bool flag) : ModulePass(ID) {
            this->flag = flag;
            funcAdd[0] = &Substitution::addNeg;
            funcAdd[1] = &Substitution::addDoubleNeg;
            funcAdd[2] = &Substitution::addRand;
            funcAdd[3] = &Substitution::addRand2;

            funcSub[0] = &Substitution::subNeg;
            funcSub[1] = &Substitution::subRand;
            funcSub[2] = &Substitution::subRand2;

            funcAnd[0] = &Substitution::andSubstitution;
            funcAnd[1] = &Substitution::andSubstitutionRand;

            funcOr[0] = &Substitution::orSubstitution;
            funcOr[1] = &Substitution::orSubstitutionRand;

            funcXor[0] = &Substitution::xorSubstitution;
            funcXor[1] = &Substitution::xorSubstitutionRand;
        }

        bool substitute(Function *f);

        bool addNeg(BinaryOperator *bo);
        bool addDoubleNeg(BinaryOperator *bo);
        bool addRand(BinaryOperator *bo);
        bool addRand2(BinaryOperator *bo);

        bool subNeg(BinaryOperator *bo);
        bool subRand(BinaryOperator *bo);
        bool subRand2(BinaryOperator *bo);

        void andSubstitution(BinaryOperator *bo);
        void andSubstitutionRand(BinaryOperator *bo);

        void orSubstitution(BinaryOperator *bo);
        void orSubstitutionRand(BinaryOperator *bo);

        void xorSubstitution(BinaryOperator *bo);
        void xorSubstitutionRand(BinaryOperator *bo);

    };

}
std::set<BasicBlock*> SplitedBasicBlocks;
char Substitution::ID = 0;
static RegisterPass<Substitution> X("substitution", "operators substitution");
Pass *llvm::createSubstitution(bool flag) { return new Substitution(flag); }

bool Substitution::runOnModule(Module &M) {

	LLVM_DEBUG(outs() << "Substitution debug!\n");
    //outs() << "kzykzykzy!\n";
    
    for (auto &F : M) {

        bool needProtect = inConfigOrRandom(ProtName, M, F, ProtRatio);
        if (needProtect) {
            LLVM_DEBUG(outs() << "func checked: " << F.getName() << "\n");
            substitute(&F);
        } else {
            LLVM_DEBUG(outs() << "func nochecked: " << F.getName() << "\n");
        }

    }
	return true;
}

bool Substitution::substitute(Function *f) {
  Function *tmp = f;
  for (Function::iterator bb = tmp->begin(); bb != tmp->end(); ++bb) {
    BasicBlock::iterator inst = bb->begin();
	if (SplitedBasicBlocks.find(&(*bb))!=SplitedBasicBlocks.end()) {
		inst++;
	}
      
    for (; inst != bb->end(); ++inst) {
      if (inst->isBinaryOp()) {
        bool splited = false;
        switch (inst->getOpcode()) {
        case BinaryOperator::Add:
          // case BinaryOperator::FAdd:
          // Substitute with random add operation
          splited = (this->*funcAdd[llvm::cryptoutils->get_range(NUMBER_ADD_SUBST)])(
              cast<BinaryOperator>(inst));
          ++Add;
          break;
        case BinaryOperator::Sub:
          // case BinaryOperator::FSub:
          // Substitute with random sub operation
          splited = (this->*funcSub[llvm::cryptoutils->get_range(NUMBER_SUB_SUBST)])(
              cast<BinaryOperator>(inst));
          ++Sub;
          break;
        case BinaryOperator::Mul:
        case BinaryOperator::FMul:
          //++Mul;
          break;
        case BinaryOperator::UDiv:
        case BinaryOperator::SDiv:
        case BinaryOperator::FDiv:
          //++Div;
          break;
        case BinaryOperator::URem:
        case BinaryOperator::SRem:
        case BinaryOperator::FRem:
          //++Rem;
          break;
        case Instruction::Shl:
          //++Shi;
          break;
        case Instruction::LShr:
          //++Shi;
          break;
        case Instruction::AShr:
          //++Shi;
          break;
        case Instruction::And:
          (this->*
            funcAnd[llvm::cryptoutils->get_range(2)])(cast<BinaryOperator>(inst));
          ++And;
          break;
        case Instruction::Or:
          (this->*
            funcOr[llvm::cryptoutils->get_range(2)])(cast<BinaryOperator>(inst));
          ++Or;
          break;
        case Instruction::Xor:
          (this->*
            funcXor[llvm::cryptoutils->get_range(2)])(cast<BinaryOperator>(inst));
          ++Xor;
          break;
        default:
          break;
        }              // End switch
        if (splited)
          break;
      }                // End isBinaryOp
    }                  // End for basickblock
  }                    // End for Function
  return false;
}

// Implementation of a = b - (-c)
bool Substitution::addNeg(BinaryOperator *bo) {
  BinaryOperator *op = NULL;
  BinaryOperator *oop = NULL;
  // Create sub
  if (bo->getOpcode() == Instruction::Add) {
      op = BinaryOperator::CreateNeg(bo->getOperand(1), "", bo);
      oop =
          BinaryOperator::Create(Instruction::Sub, bo->getOperand(0), op, "", bo);
      bo->replaceAllUsesWith(oop);
      bo->eraseFromParent();
      BasicBlock *newBB = oop->getParent()->splitBasicBlock(oop, "codeprot_sub");
	  SplitedBasicBlocks.insert(newBB);
      BlockAddress *NewBBAddr = BlockAddress::get(newBB);
      if(oop->getParent() != &(oop->getParent()->getParent()->getEntryBlock())){
        BlockAddress *oldBBAddr = BlockAddress::get(oop->getParent());
      }
      return true;
  }
  return false;
}

// Implementation of a = -(-b + (-c))
bool Substitution::addDoubleNeg(BinaryOperator *bo) {
  BinaryOperator *op, *op2,*op3 = NULL;

  if (bo->getOpcode() == Instruction::Add) {
    op = BinaryOperator::CreateNeg(bo->getOperand(0), "", bo);
    op2 = BinaryOperator::CreateNeg(bo->getOperand(1), "", bo);
    op3 = BinaryOperator::Create(Instruction::Add, op, op2, "", bo);
    op = BinaryOperator::CreateNeg(op3, "", bo);

    // Check signed wrap
    //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
    //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());
  } else {
    op = BinaryOperator::CreateFNeg(bo->getOperand(0), "", bo);
    op2 = BinaryOperator::CreateFNeg(bo->getOperand(1), "", bo);
    op = BinaryOperator::Create(Instruction::FAdd, op, op2, "", bo);
    op = BinaryOperator::CreateFNeg(op, "", bo);
  }
  bo->replaceAllUsesWith(op);


  bo->eraseFromParent();
  BasicBlock *newBB = op3->getParent()->splitBasicBlock(op3, "codeprot_addDoubleNeg");
  SplitedBasicBlocks.insert(newBB);
  BlockAddress *NewBBAddr = BlockAddress::get(newBB);
  if(op3->getParent() != &(op3->getParent()->getParent()->getEntryBlock())){
    BlockAddress *oldBBAddr = BlockAddress::get(op2->getParent());
  }
  return true;
  if (bo->getOpcode() != Instruction::Add) {
    return false;
  }
}

// Implementation of  r = rand (); a = b + r; a = a + c; a = a - r
bool Substitution::addRand(BinaryOperator *bo) {
  BinaryOperator *op, *op1, *op2 = NULL;

  if (bo->getOpcode() == Instruction::Add) {
    //outs() << "rand" << bo->getParent()->getParent()->getName() << "\n";
    Type *ty = bo->getType();
    ConstantInt *co =
        (ConstantInt *)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());
    op =
        BinaryOperator::Create(Instruction::Add, bo->getOperand(0), co, "", bo);
    op1 =
        BinaryOperator::Create(Instruction::Add, op, bo->getOperand(1), "", bo);
    op2 = BinaryOperator::Create(Instruction::Sub, op1, co, "", bo);

    // Check signed wrap
    //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
    //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());

    bo->replaceAllUsesWith(op2);
    bo->eraseFromParent();
    BasicBlock *newBB = op2->getParent()->splitBasicBlock(op2, "codeprot_addRand");
	SplitedBasicBlocks.insert(newBB);
    BlockAddress *NewBBAddr = BlockAddress::get(newBB);
    if(op->getParent() != &(op->getParent()->getParent()->getEntryBlock())){
      BlockAddress *oldBBAddr = BlockAddress::get(op->getParent());
    }
    return true;
  }
  /* else {
      Type *ty = bo->getType();
      ConstantFP *co =
  (ConstantFP*)ConstantFP::get(ty,(float)llvm::cryptoutils->get_uint64_t());
      op = BinaryOperator::Create(Instruction::FAdd,bo->getOperand(0),co,"",bo);
      op = BinaryOperator::Create(Instruction::FAdd,op,bo->getOperand(1),"",bo);
      op = BinaryOperator::Create(Instruction::FSub,op,co,"",bo);
  } */
  return false;
}

// Implementation of r = rand (); a = b - r; a = a + b; a = a + r
bool Substitution::addRand2(BinaryOperator *bo) {
  BinaryOperator *op, *op1, *op2 = NULL;

  if (bo->getOpcode() == Instruction::Add) {
    Type *ty = bo->getType();
    ConstantInt *co =
        (ConstantInt *)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());
    op =
        BinaryOperator::Create(Instruction::Sub, bo->getOperand(0), co, "", bo);
    op1 =
        BinaryOperator::Create(Instruction::Add, op, bo->getOperand(1), "", bo);
    op2 = BinaryOperator::Create(Instruction::Add, op1, co, "", bo);

    // Check signed wrap
    //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
    //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());

    bo->replaceAllUsesWith(op2);
    bo->eraseFromParent();
    BasicBlock *newBB = op2->getParent()->splitBasicBlock(op2, "codeprot_addRand2");
	SplitedBasicBlocks.insert(newBB);
    BlockAddress *NewBBAddr = BlockAddress::get(newBB);
    if(op->getParent() != &(op->getParent()->getParent()->getEntryBlock())){
      BlockAddress *oldBBAddr = BlockAddress::get(op->getParent());
    }
    return true;
  }
  /* else {
      Type *ty = bo->getType();
      ConstantFP *co =
  (ConstantFP*)ConstantFP::get(ty,(float)llvm::cryptoutils->get_uint64_t());
      op = BinaryOperator::Create(Instruction::FAdd,bo->getOperand(0),co,"",bo);
      op = BinaryOperator::Create(Instruction::FAdd,op,bo->getOperand(1),"",bo);
      op = BinaryOperator::Create(Instruction::FSub,op,co,"",bo);
  } */
  return false;
}

// Implementation of a = b + (-c)
bool Substitution::subNeg(BinaryOperator *bo) {
  BinaryOperator *op, *oop = NULL;

  if (bo->getOpcode() == Instruction::Sub) {
    op = BinaryOperator::CreateNeg(bo->getOperand(1), "", bo);
    oop =
        BinaryOperator::Create(Instruction::Add, bo->getOperand(0), op, "", bo);
    bo->replaceAllUsesWith(oop);
    bo->eraseFromParent();
    BasicBlock *newBB = oop->getParent()->splitBasicBlock(oop, "codeprot_sub");
	SplitedBasicBlocks.insert(newBB);
    BlockAddress *NewBBAddr = BlockAddress::get(newBB);
    if(op->getParent() != &(op->getParent()->getParent()->getEntryBlock())){
      BlockAddress *oldBBAddr = BlockAddress::get(op->getParent());
    }
    return true;
    // Check signed wrap
    //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
    //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());
  } else {
    op = BinaryOperator::CreateFNeg(bo->getOperand(1), "", bo);
    op = BinaryOperator::Create(Instruction::FAdd, bo->getOperand(0), op, "",
                                bo);
  }
  return false;
}

// Implementation of  r = rand (); a = b + r; a = a - c; a = a - r
bool Substitution::subRand(BinaryOperator *bo) {
  BinaryOperator *op, *op1, *op2 = NULL;

  if (bo->getOpcode() == Instruction::Sub) {
    Type *ty = bo->getType();
    ConstantInt *co =
        (ConstantInt *)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());
    op =
        BinaryOperator::Create(Instruction::Add, bo->getOperand(0), co, "", bo);
    op1 =
        BinaryOperator::Create(Instruction::Sub, op, bo->getOperand(1), "", bo);
    op2 = BinaryOperator::Create(Instruction::Sub, op1, co, "", bo);

    // Check signed wrap
    //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
    //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());
    bo->replaceAllUsesWith(op2);
    bo->eraseFromParent();
    BasicBlock *newBB = op2->getParent()->splitBasicBlock(op2, "codeprot_addRand2");
	SplitedBasicBlocks.insert(newBB);
    BlockAddress *NewBBAddr = BlockAddress::get(newBB);
    if(op->getParent() != &(op->getParent()->getParent()->getEntryBlock())){
      BlockAddress *oldBBAddr = BlockAddress::get(op->getParent());
    }
    return true;
  }
  /* else {
      Type *ty = bo->getType();
      ConstantFP *co =
  (ConstantFP*)ConstantFP::get(ty,(float)llvm::cryptoutils->get_uint64_t());
      op = BinaryOperator::Create(Instruction::FAdd,bo->getOperand(0),co,"",bo);
      op = BinaryOperator::Create(Instruction::FSub,op,bo->getOperand(1),"",bo);
      op = BinaryOperator::Create(Instruction::FSub,op,co,"",bo);
  } */
  return false;
}

// Implementation of  r = rand (); a = b - r; a = a - c; a = a + r
bool Substitution::subRand2(BinaryOperator *bo) {
  BinaryOperator *op, *op1, *op2 = NULL;

  if (bo->getOpcode() == Instruction::Sub) {
    Type *ty = bo->getType();
    ConstantInt *co =
        (ConstantInt *)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());
    op =
        BinaryOperator::Create(Instruction::Sub, bo->getOperand(0), co, "", bo);
    op1 =
        BinaryOperator::Create(Instruction::Sub, op, bo->getOperand(1), "", bo);
    op2 = BinaryOperator::Create(Instruction::Add, op1, co, "", bo);

    // Check signed wrap
    //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
    //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());

    bo->replaceAllUsesWith(op2);
    bo->eraseFromParent();
    BasicBlock *newBB = op2->getParent()->splitBasicBlock(op2, "codeprot_addRand2");
	SplitedBasicBlocks.insert(newBB);
    BlockAddress *NewBBAddr = BlockAddress::get(newBB);
    if(op->getParent() != &(op->getParent()->getParent()->getEntryBlock())){
      BlockAddress *oldBBAddr = BlockAddress::get(op->getParent());
    }
    return true;
  }
  /* else {
      Type *ty = bo->getType();
      ConstantFP *co =
  (ConstantFP*)ConstantFP::get(ty,(float)llvm::cryptoutils->get_uint64_t());
      op = BinaryOperator::Create(Instruction::FSub,bo->getOperand(0),co,"",bo);
      op = BinaryOperator::Create(Instruction::FSub,op,bo->getOperand(1),"",bo);
      op = BinaryOperator::Create(Instruction::FAdd,op,co,"",bo);
  } */
  return false;
}

// Implementation of a = b & c => a = (b^~c)& b
void Substitution::andSubstitution(BinaryOperator *bo) {
  BinaryOperator *op = NULL;

  // Create NOT on second operand => ~c
  op = BinaryOperator::CreateNot(bo->getOperand(1), "", bo);

  // Create XOR => (b^~c)
  BinaryOperator *op1 =
      BinaryOperator::Create(Instruction::Xor, bo->getOperand(0), op, "", bo);

  // Create AND => (b^~c) & b
  op = BinaryOperator::Create(Instruction::And, op1, bo->getOperand(0), "", bo);
  bo->replaceAllUsesWith(op);
}

// Implementation of a = a && b <=> !(!a | !b) && (r | !r)
void Substitution::andSubstitutionRand(BinaryOperator *bo) {
  // Copy of the BinaryOperator type to create the random number with the
  // same type of the operands
  Type *ty = bo->getType();

  // r (Random number)
  ConstantInt *co =
      (ConstantInt *)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());

  // !a
  BinaryOperator *op = BinaryOperator::CreateNot(bo->getOperand(0), "", bo);

  // !b
  BinaryOperator *op1 = BinaryOperator::CreateNot(bo->getOperand(1), "", bo);

  // !r
  BinaryOperator *opr = BinaryOperator::CreateNot(co, "", bo);

  // (!a | !b)
  BinaryOperator *opa =
      BinaryOperator::Create(Instruction::Or, op, op1, "", bo);

  // (r | !r)
  opr = BinaryOperator::Create(Instruction::Or, co, opr, "", bo);

  // !(!a | !b)
  op = BinaryOperator::CreateNot(opa, "", bo);

  // !(!a | !b) && (r | !r)
  op = BinaryOperator::Create(Instruction::And, op, opr, "", bo);

  // We replace all the old AND operators with the new one transformed
  bo->replaceAllUsesWith(op);
}

// Implementation of a = b | c => a = (b & c) | (b ^ c)
void Substitution::orSubstitutionRand(BinaryOperator *bo) {

  Type *ty = bo->getType();
  ConstantInt *co =
      (ConstantInt *)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());

  // !a
  BinaryOperator *op = BinaryOperator::CreateNot(bo->getOperand(0), "", bo);

  // !b
  BinaryOperator *op1 = BinaryOperator::CreateNot(bo->getOperand(1), "", bo);

  // !r
  BinaryOperator *op2 = BinaryOperator::CreateNot(co, "", bo);

  // !a && r
  BinaryOperator *op3 =
      BinaryOperator::Create(Instruction::And, op, co, "", bo);

  // a && !r
  BinaryOperator *op4 =
      BinaryOperator::Create(Instruction::And, bo->getOperand(0), op2, "", bo);

  // !b && r
  BinaryOperator *op5 =
      BinaryOperator::Create(Instruction::And, op1, co, "", bo);

  // b && !r
  BinaryOperator *op6 =
      BinaryOperator::Create(Instruction::And, bo->getOperand(1), op2, "", bo);

  // (!a && r) || (a && !r)
  op3 = BinaryOperator::Create(Instruction::Or, op3, op4, "", bo);

  // (!b && r) ||(b && !r)
  op4 = BinaryOperator::Create(Instruction::Or, op5, op6, "", bo);

  // (!a && r) || (a && !r) ^ (!b && r) ||(b && !r)
  op5 = BinaryOperator::Create(Instruction::Xor, op3, op4, "", bo);

  // !a || !b
  op3 = BinaryOperator::Create(Instruction::Or, op, op1, "", bo);

  // !(!a || !b)
  op3 = BinaryOperator::CreateNot(op3, "", bo);

  // r || !r
  op4 = BinaryOperator::Create(Instruction::Or, co, op2, "", bo);

  // !(!a || !b) && (r || !r)
  op4 = BinaryOperator::Create(Instruction::And, op3, op4, "", bo);

  // [(!a && r) || (a && !r) ^ (!b && r) ||(b && !r) ] || [!(!a || !b) && (r ||
  // !r)]
  op = BinaryOperator::Create(Instruction::Or, op5, op4, "", bo);
  bo->replaceAllUsesWith(op);
}

void Substitution::orSubstitution(BinaryOperator *bo) {
  BinaryOperator *op = NULL;

  // Creating first operand (b & c)
  op = BinaryOperator::Create(Instruction::And, bo->getOperand(0),
                              bo->getOperand(1), "", bo);

  // Creating second operand (b ^ c)
  BinaryOperator *op1 = BinaryOperator::Create(
      Instruction::Xor, bo->getOperand(0), bo->getOperand(1), "", bo);

  // final op
  op = BinaryOperator::Create(Instruction::Or, op, op1, "", bo);
  bo->replaceAllUsesWith(op);
}

// Implementation of a = a ~ b => a = (!a && b) || (a && !b)
void Substitution::xorSubstitution(BinaryOperator *bo) {
  BinaryOperator *op = NULL;

  // Create NOT on first operand
  op = BinaryOperator::CreateNot(bo->getOperand(0), "", bo); // !a

  // Create AND
  op = BinaryOperator::Create(Instruction::And, bo->getOperand(1), op, "",
                              bo); // !a && b

  // Create NOT on second operand
  BinaryOperator *op1 =
      BinaryOperator::CreateNot(bo->getOperand(1), "", bo); // !b

  // Create AND
  op1 = BinaryOperator::Create(Instruction::And, bo->getOperand(0), op1, "",
                               bo); // a && !b

  // Create OR
  op = BinaryOperator::Create(Instruction::Or, op, op1, "",
                              bo); // (!a && b) || (a && !b)
  bo->replaceAllUsesWith(op);
}

// implementation of a = a ^ b <=> (a ^ r) ^ (b ^ r) <=> (!a && r || a && !r) ^
// (!b && r || b && !r)
// note : r is a random number
void Substitution::xorSubstitutionRand(BinaryOperator *bo) {
  BinaryOperator *op = NULL;

  Type *ty = bo->getType();
  ConstantInt *co =
      (ConstantInt *)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());

  // !a
  op = BinaryOperator::CreateNot(bo->getOperand(0), "", bo);

  // !a && r
  op = BinaryOperator::Create(Instruction::And, co, op, "", bo);

  // !r
  BinaryOperator *opr = BinaryOperator::CreateNot(co, "", bo);

  // a && !r
  BinaryOperator *op1 =
      BinaryOperator::Create(Instruction::And, bo->getOperand(0), opr, "", bo);

  // !b
  BinaryOperator *op2 = BinaryOperator::CreateNot(bo->getOperand(1), "", bo);

  // !b && r
  op2 = BinaryOperator::Create(Instruction::And, op2, co, "", bo);

  // b && !r
  BinaryOperator *op3 =
      BinaryOperator::Create(Instruction::And, bo->getOperand(1), opr, "", bo);

  // (!a && r) || (a && !r)
  op = BinaryOperator::Create(Instruction::Or, op, op1, "", bo);

  // (!b && r) || (b && !r)
  op1 = BinaryOperator::Create(Instruction::Or, op2, op3, "", bo);

  // (!a && r) || (a && !r) ^ (!b && r) || (b && !r)
  op = BinaryOperator::Create(Instruction::Xor, op, op1, "", bo);
  bo->replaceAllUsesWith(op);
}

