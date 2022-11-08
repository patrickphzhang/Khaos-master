//===- BogusControlFlow.cpp -------------------------------------
//---------------===//
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
#include "llvm/IR/DebugInfo.h"

#define DEBUG_TYPE "boguscf"

namespace {
struct BogusControlFlow : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  bool flag;
  const string ProtName = PROTNAME_OBFUSCATION;
  const int ProtRatio = RatioObfuscation;
  BogusControlFlow() : ModulePass(ID) {}
  BogusControlFlow(bool flag) : ModulePass(ID) {
    this->flag = flag;
    BogusControlFlow();
  }

  bool runOnModule(Module &M) override;
  void bogus(Function &M);
  virtual void addBogusFlow(BasicBlock *basicBlock, Function &F);
  virtual BasicBlock *createAlteredBasicBlock(BasicBlock *basicBlock,
                                              const Twine &Name = "gen",
                                              Function *F = 0);
  bool doF(Module &M);
};
} // namespace

char BogusControlFlow::ID = 0;

bool BogusControlFlow::runOnModule(Module &M) {
  //outs() << "In BogusControlFlow!\n";
  
  LLVM_DEBUG(outs() << "BogusControlFlow debug!\n");
  bool flag = 0;
  for (auto &F : M) {
    bool needProtect = inConfigOrRandom(ProtName, M, F, ProtRatio);
    if (needProtect) {
      LLVM_DEBUG(outs() << "func checked: " << F.getName() << "\n");

      // F.viewCFG();
      bogus(F);

      flag = 1;
    } else {
      LLVM_DEBUG(outs() << "func nochecked: " << F.getName() << "\n");
    }
  }

  if (flag) {
    doF(M);
    // M.getFunction("main")->viewCFG();
  }

  return flag;
}

void BogusControlFlow::bogus(Function &F) {
  std::list<BasicBlock *> basicBlocks;
  for (auto &BB : F)
    basicBlocks.push_back(&BB);

  basicBlocks.pop_front();

  for (auto BB : basicBlocks) {
    // bool HasInvoke = 0;

    if (BB->getTerminator()->isExceptionalTerminator() || BB->isEHPad()||BB==basicBlocks.front())
      continue;

    // for (auto &ins : *basicBlock)
    //   if (ins.getOpcode() == Instruction::Invoke) { // ins.isEHPad() ||
    //   ins.isExceptionalTerminator()) {
    //     HasInvoke = true;
    //     break;
    //   }
    // if (!HasInvoke)
    addBogusFlow(BB, F);
  }
}

void BogusControlFlow::addBogusFlow(BasicBlock *basicBlock, Function &F) {

  BasicBlock::iterator i1 = basicBlock->begin();
  if (basicBlock->getFirstNonPHIOrDbgOrLifetime())
    i1 = (BasicBlock::iterator)basicBlock->getFirstNonPHIOrDbgOrLifetime();
  Twine *var = new Twine("originalBB");
  BasicBlock *originalBB = basicBlock->splitBasicBlock(i1, *var);

  // Creating the altered basic block on which the first basicBlock will jump
  Twine *var3 = new Twine("alteredBB");
  BasicBlock *alteredBB = createAlteredBasicBlock(originalBB, *var3, &F);

  // Now that all the blocks are created,
  // we modify the terminators to adjust the control flow.

  alteredBB->getTerminator()->eraseFromParent();
  basicBlock->getTerminator()->eraseFromParent();

  // Preparing a condition..
  // For now, the condition is an always true comparaison between 2 float
  // This will be complicated after the pass (in doFinalization())
  Value *LHS = ConstantFP::get(Type::getFloatTy(F.getContext()), 1.0);
  Value *RHS = ConstantFP::get(Type::getFloatTy(F.getContext()), 1.0);

  // The always true condition. End of the first block
  Twine *var4 = new Twine("condition");
  FCmpInst *condition =
      new FCmpInst(*basicBlock, FCmpInst::FCMP_TRUE, LHS, RHS, *var4);

  // Jump to the original basic block if the condition is true or
  // to the altered block if false.
  BranchInst::Create(originalBB, alteredBB, (Value *)condition, basicBlock);

  // The altered block loop back on the original one.
  BranchInst::Create(originalBB, alteredBB);

  // The end of the originalBB is modified to give the impression that sometimes
  // it continues in the loop, and sometimes it return the desired value
  // (of course it's always true, so it always use the original terminator..
  //  but this will be obfuscated too;) )

  // iterate on instruction just before the terminator of the originalBB
  BasicBlock::iterator i = originalBB->end();

  // Split at this point (we only want the terminator in the second part)
  Twine *var5 = new Twine("originalBBpart2");
  BasicBlock *originalBBpart2 = originalBB->splitBasicBlock(--i, *var5);
  // the first part go either on the return statement or on the begining
  // of the altered block.. So we erase the terminator created when splitting.
  originalBB->getTerminator()->eraseFromParent();
  // We add at the end a new always true condition
  Twine *var6 = new Twine("condition2");
  FCmpInst *condition2 =
      new FCmpInst(*originalBB, CmpInst::FCMP_TRUE, LHS, RHS, *var6);
  BranchInst::Create(originalBBpart2, alteredBB, (Value *)condition2,
                     originalBB);
}

BasicBlock *BogusControlFlow::createAlteredBasicBlock(BasicBlock *basicBlock,
                                                      const Twine &Name,
                                                      Function *F) {
  ValueToValueMapTy VMap;
  BasicBlock *alteredBB = llvm::CloneBasicBlock(basicBlock, VMap, Name, F);


  //BasicBlock::iterator inst = alteredBB->begin();
  // Remap operands.
  
  BasicBlock::iterator ji = basicBlock->begin();
  for (BasicBlock::iterator i = alteredBB->begin(), e = alteredBB->end();
       i != e; ++i) {
    //i->dump();
    
    // Loop over the operands of the instruction
    for (User::op_iterator opi = i->op_begin(), ope = i->op_end(); opi != ope;
         ++opi) {
      // get the value for the operand
      Value *v = MapValue(*opi, VMap, RF_None, 0);
      if (v != 0) {
        *opi = v;
      }
    }
    // Remap phi nodes' incoming blocks.
    if (PHINode *pn = dyn_cast<PHINode>(i)) {
      for (unsigned j = 0, e = pn->getNumIncomingValues(); j != e; ++j) {
        Value *v = MapValue(pn->getIncomingBlock(j), VMap, RF_None, 0);
        if (v != 0) {
          pn->setIncomingBlock(j, cast<BasicBlock>(v));
        }
      }
    }
    // Remap attached metadata.
    if(isa<DbgInfoIntrinsic>(i)){
      //i->dump();
      //i->eraseFromParent();
      continue;
    }
    SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
    i->getAllMetadata(MDs);
    // important for compiling with DWARF, using option -g.
    
    i->setDebugLoc(ji->getDebugLoc());
    ji++;

  } // The instructions' informations are now all correct

  // add random instruction in the middle of the bloc. This part can be improve
  for (BasicBlock::iterator i = alteredBB->begin(), e = alteredBB->end();
       i != e; ++i) {
    // in the case we find binary operator, we modify slightly this part by
    // randomly insert some instructions
    if (i->isBinaryOp()) { // binary instructions
      unsigned opcode = i->getOpcode();
      BinaryOperator *op, *op1 = NULL;
      Twine *var = new Twine("_");
      // treat differently float or int
      // Binary int
      if (opcode == Instruction::Add || opcode == Instruction::Sub ||
          opcode == Instruction::Mul || opcode == Instruction::UDiv ||
          opcode == Instruction::SDiv || opcode == Instruction::URem ||
          opcode == Instruction::SRem || opcode == Instruction::Shl ||
          opcode == Instruction::LShr || opcode == Instruction::AShr ||
          opcode == Instruction::And || opcode == Instruction::Or ||
          opcode == Instruction::Xor) {
        for (int random = rand() % (10); random < 10; ++random) {
          switch (rand() % (4)) { // to improve
          case 0:                 // do nothing
            break;
          case 1:
            op = BinaryOperator::CreateNeg(i->getOperand(0), *var, &*i);
            op1 = BinaryOperator::Create(Instruction::Add, op, i->getOperand(1),
                                         "gen", &*i);
            break;
          case 2:
            op1 = BinaryOperator::Create(Instruction::Sub, i->getOperand(0),
                                         i->getOperand(1), *var, &*i);
            op = BinaryOperator::Create(Instruction::Mul, op1, i->getOperand(1),
                                        "gen", &*i);
            break;
          case 3:
            op = BinaryOperator::Create(Instruction::Shl, i->getOperand(0),
                                        i->getOperand(1), *var, &*i);
            break;
          }
        }
      }
      // Binary float
      if (opcode == Instruction::FAdd || opcode == Instruction::FSub ||
          opcode == Instruction::FMul || opcode == Instruction::FDiv ||
          opcode == Instruction::FRem) {
        for (int random = rand() % (10); random < 10; ++random) {
          switch (rand() % (3)) { // can be improved
          case 0:                 // do nothing
            break;
          case 1:
            op = BinaryOperator::CreateFNeg(i->getOperand(0), *var, &*i);
            op1 = BinaryOperator::Create(Instruction::FAdd, op,
                                         i->getOperand(1), "gen", &*i);
            break;
          case 2:
            op = BinaryOperator::Create(Instruction::FSub, i->getOperand(0),
                                        i->getOperand(1), *var, &*i);
            op1 = BinaryOperator::Create(Instruction::FMul, op,
                                         i->getOperand(1), "gen", &*i);
            break;
          }
        }
      }
      if (opcode == Instruction::ICmp) { // Condition (with int)
        ICmpInst *currentI = (ICmpInst *)(&i);
        switch (rand() % (3)) { // must be improved
        case 0:                 // do nothing
          break;
        case 1:
          currentI->swapOperands();
          break;
        case 2: // randomly change the predicate
          switch (rand() % (10)) {
          case 0:
            currentI->setPredicate(ICmpInst::ICMP_EQ);
            break; // equal
          case 1:
            currentI->setPredicate(ICmpInst::ICMP_NE);
            break; // not equal
          case 2:
            currentI->setPredicate(ICmpInst::ICMP_UGT);
            break; // unsigned greater than
          case 3:
            currentI->setPredicate(ICmpInst::ICMP_UGE);
            break; // unsigned greater or equal
          case 4:
            currentI->setPredicate(ICmpInst::ICMP_ULT);
            break; // unsigned less than
          case 5:
            currentI->setPredicate(ICmpInst::ICMP_ULE);
            break; // unsigned less or equal
          case 6:
            currentI->setPredicate(ICmpInst::ICMP_SGT);
            break; // signed greater than
          case 7:
            currentI->setPredicate(ICmpInst::ICMP_SGE);
            break; // signed greater or equal
          case 8:
            currentI->setPredicate(ICmpInst::ICMP_SLT);
            break; // signed less than
          case 9:
            currentI->setPredicate(ICmpInst::ICMP_SLE);
            break; // signed less or equal
          }
          break;
        }
      }
      if (opcode == Instruction::FCmp) { // Conditions (with float)
        FCmpInst *currentI = (FCmpInst *)(&i);
        switch (rand() % (3)) { // must be improved
        case 0:                 // do nothing
          break;
        case 1:
          currentI->swapOperands();
          break;
        case 2: // randomly change the predicate
          switch (rand() % (10)) {
          case 0:
            currentI->setPredicate(FCmpInst::FCMP_OEQ);
            break; // ordered and equal
          case 1:
            currentI->setPredicate(FCmpInst::FCMP_ONE);
            break; // ordered and operands are unequal
          case 2:
            currentI->setPredicate(FCmpInst::FCMP_UGT);
            break; // unordered or greater than
          case 3:
            currentI->setPredicate(FCmpInst::FCMP_UGE);
            break; // unordered, or greater than, or equal
          case 4:
            currentI->setPredicate(FCmpInst::FCMP_ULT);
            break; // unordered or less than
          case 5:
            currentI->setPredicate(FCmpInst::FCMP_ULE);
            break; // unordered, or less than, or equal
          case 6:
            currentI->setPredicate(FCmpInst::FCMP_OGT);
            break; // ordered and greater than
          case 7:
            currentI->setPredicate(FCmpInst::FCMP_OGE);
            break; // ordered and greater than or equal
          case 8:
            currentI->setPredicate(FCmpInst::FCMP_OLT);
            break; // ordered and less than
          case 9:
            currentI->setPredicate(FCmpInst::FCMP_OLE);
            break; // ordered or less than, or equal
          }
          break;
        }
      }
    }
  }

  return alteredBB;
}

/*void BogusControlFlow::doF(Module &M) {

  //  The global values
  Twine *varX = new Twine("x");
  Twine *varY = new Twine("y");
  Value *x1 = ConstantInt::get(Type::getInt32Ty(M.getContext()), 0, false);
  Value *y1 = ConstantInt::get(Type::getInt32Ty(M.getContext()), 0, false);

  GlobalVariable *x =
      new GlobalVariable(M, Type::getInt32Ty(M.getContext()), false,
                         GlobalValue::CommonLinkage, (Constant *)x1, *varX);
  GlobalVariable *y =
      new GlobalVariable(M, Type::getInt32Ty(M.getContext()), false,
                         GlobalValue::CommonLinkage, (Constant *)y1, *varY);

  std::vector<Instruction *> toEdit, toDelete;
  BinaryOperator *op, *op1 = NULL;
  LoadInst *opX, *opY;
  ICmpInst *condition, *condition2;
  // Looking for the conditions and branches to transform
  for (Module::iterator mi = M.begin(), me = M.end(); mi != me; ++mi) {
    for (Function::iterator fi = mi->begin(), fe = mi->end(); fi != fe; ++fi) {
      // fi->setName("");
      Instruction *tbb = fi->getTerminator();
      if (tbb->getOpcode() == Instruction::Br) {
        BranchInst *br = (BranchInst *)(tbb);
        if (br->isConditional()) {
          FCmpInst *cond = (FCmpInst *)br->getCondition();
          unsigned opcode = cond->getOpcode();
          if (opcode == Instruction::FCmp) {
            if (cond->getPredicate() == FCmpInst::FCMP_TRUE) {
              DEBUG_WITH_TYPE("gen",
                              errs() << "bcf: an always true predicate !\n");
              toDelete.push_back(cond); // The condition
              toEdit.push_back(tbb);    // The branch using the condition
            }
          }
        }
      }
    }
  }
  // Replacing all the branches we found
  for (auto i : toEdit) {
    // if y < 10 || x*(x+1) % 2 == 0
    opX = new LoadInst(cast<Value>(x), "", i);
    opY = new LoadInst(cast<Value>(y), "", i);

    op = BinaryOperator::Create(
        Instruction::Sub, cast<Value>(opX),
        ConstantInt::get(Type::getInt32Ty(M.getContext()), 1, false), "", i);
    op1 = BinaryOperator::Create(Instruction::Mul, cast<Value>(opX), op, "", i);
    op = BinaryOperator::Create(
        Instruction::URem, op1,
        ConstantInt::get(Type::getInt32Ty(M.getContext()), 2, false), "", i);
    condition = new ICmpInst(
        i, ICmpInst::ICMP_EQ, op,
        ConstantInt::get(Type::getInt32Ty(M.getContext()), 0, false));
    condition2 = new ICmpInst(
        i, ICmpInst::ICMP_SLT, opY,
        ConstantInt::get(Type::getInt32Ty(M.getContext()), 10, false));
    op1 = BinaryOperator::Create(Instruction::Or, cast<Value>(condition),
                                 cast<Value>(condition2), "", i);

    BranchInst::Create(cast<BranchInst>(i)->getSuccessor(0),
                       cast<BranchInst>(i)->getSuccessor(1), (Value *)op1,
                       cast<BranchInst>(i)->getParent());
    i->eraseFromParent(); // erase the branch
  }

  // Erase all the associated conditions we found
  for (auto i : toDelete) {
    i->eraseFromParent();
  }
  return;
}
*/
bool BogusControlFlow::doF(Module &M){
      // In this part we extract all always-true predicate and replace them with opaque predicate:
      // For this, we declare two global values: x and y, and replace the FCMP_TRUE predicate with
      // (y < 10 || x * (x + 1) % 2 == 0)
      // A better way to obfuscate the predicates would be welcome.
      // In the meantime we will erase the name of the basic blocks, the instructions
      // and the functions.
      DEBUG_WITH_TYPE("gen", errs()<<"bcf: Starting doFinalization...\n");

      //  The global values
      Twine * varX = new Twine("x");
      Twine * varY = new Twine("y");
      Value * x1 =ConstantInt::get(Type::getInt32Ty(M.getContext()), 0, false);
      Value * y1 =ConstantInt::get(Type::getInt32Ty(M.getContext()), 0, false);

      GlobalVariable 	* x = new GlobalVariable(M, Type::getInt32Ty(M.getContext()), false,
          GlobalValue::CommonLinkage, (Constant * )x1,
          *varX);
      GlobalVariable 	* y = new GlobalVariable(M, Type::getInt32Ty(M.getContext()), false,
          GlobalValue::CommonLinkage, (Constant * )y1,
          *varY);


      std::vector<Instruction*> toEdit, toDelete;
      BinaryOperator *op,*op1 = NULL;
      LoadInst * opX , * opY;
      ICmpInst * condition, * condition2;
      // Looking for the conditions and branches to transform
      for(Module::iterator mi = M.begin(), me = M.end(); mi != me; ++mi){
        for(Function::iterator fi = mi->begin(), fe = mi->end(); fi != fe; ++fi){
          //fi->setName("");
          Instruction *tbb = fi->getTerminator();
          if(tbb->getOpcode() == Instruction::Br){
            BranchInst * br = (BranchInst *)(tbb);
            if(br->isConditional()){
              FCmpInst * cond = (FCmpInst *)br->getCondition();
              unsigned opcode = cond->getOpcode();
              if(opcode == Instruction::FCmp){
                if (cond->getPredicate() == FCmpInst::FCMP_TRUE){
                  DEBUG_WITH_TYPE("gen",
                      errs()<<"bcf: an always true predicate !\n");
                  toDelete.push_back(cond); // The condition
                  toEdit.push_back(tbb);    // The branch using the condition
                }
              }
            }
          }
          /*
          for (BasicBlock::iterator bi = fi->begin(), be = fi->end() ; bi != be; ++bi){
            bi->setName(""); // setting the basic blocks' names
          }
          */
        }
      }
      // Replacing all the branches we found
      for(std::vector<Instruction*>::iterator i =toEdit.begin();i!=toEdit.end();++i){
        //if y < 10 || x*(x+1) % 2 == 0
        opX = new LoadInst ((Value *)x, "", (*i));
        opY = new LoadInst ((Value *)y, "", (*i));

        op = BinaryOperator::Create(Instruction::Sub, (Value *)opX,
            ConstantInt::get(Type::getInt32Ty(M.getContext()), 1,
              false), "", (*i));
        op1 = BinaryOperator::Create(Instruction::Mul, (Value *)opX, op, "", (*i));
        op = BinaryOperator::Create(Instruction::URem, op1,
            ConstantInt::get(Type::getInt32Ty(M.getContext()), 2,
              false), "", (*i));
        condition = new ICmpInst((*i), ICmpInst::ICMP_EQ, op,
            ConstantInt::get(Type::getInt32Ty(M.getContext()), 0,
              false));
        condition2 = new ICmpInst((*i), ICmpInst::ICMP_SLT, opY,
            ConstantInt::get(Type::getInt32Ty(M.getContext()), 10,
              false));
        op1 = BinaryOperator::Create(Instruction::Or, (Value *)condition,
            (Value *)condition2, "", (*i));

        BranchInst::Create(((BranchInst*)*i)->getSuccessor(0),
            ((BranchInst*)*i)->getSuccessor(1),(Value *) op1,
            ((BranchInst*)*i)->getParent());
        DEBUG_WITH_TYPE("gen", errs() << "bcf: Erase branch instruction:"
            << *((BranchInst*)*i) << "\n");
        (*i)->eraseFromParent(); // erase the branch
      }
      // Erase all the associated conditions we found
      for(std::vector<Instruction*>::iterator i =toDelete.begin();i!=toDelete.end();++i){
        DEBUG_WITH_TYPE("gen", errs() << "bcf: Erase condition instruction:"
            << *((Instruction*)*i)<< "\n");
        (*i)->eraseFromParent();
      }

      // Only for debug
      DEBUG_WITH_TYPE("cfg",
          errs() << "bcf: End of the pass, here are the graphs after doFinalization\n");
      for(Module::iterator mi = M.begin(), me = M.end(); mi != me; ++mi){
        DEBUG_WITH_TYPE("cfg", errs() << "bcf: Function " << mi->getName() <<"\n");
        DEBUG_WITH_TYPE("cfg", mi->viewCFG());
      }
      return true;
    } // end of doFinalization

static RegisterPass<BogusControlFlow> X("boguscf", "BogusControlFlow Pass");

Pass *llvm::createBogus() { return new BogusControlFlow(); }

Pass *llvm::createBogus(bool flag) { return new BogusControlFlow(flag); }
