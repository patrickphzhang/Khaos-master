#include "llvm/Transforms/CodeProt/AntiDump.h"
#include "llvm/AsmParser/Parser.h"
#include "llvm/Support/SourceMgr.h"
#include "gtest/gtest.h"
using namespace llvm ;
namespace{
struct AntiDumpPass;
    TEST(AntiDumpPass, InsertHelper) {
    LLVMContext Ctx;
    SMDiagnostic Err;
    std::unique_ptr<Module> M(parseAssemblyString(R"invalid(
    define i32 @main(i32 %x, i32 %y, i32 %z) {
    header:
      %0 = add i32 %x, 2
      ret i32 %0
    }
  )invalid",
                                                Err, Ctx));
    codeprot::AntiDumpPass antidump;
    bool ret;
    ret = antidump.InsertHelperFunction(*M);
    // If Insert Success, the above function must return true
    EXPECT_EQ(ret,true);
    Function *Func =  M->getFunction("main");
    Instruction &firstInstruction = Func->front().front();
    // After Insert, The fisrt instruction in main func must be a CallInst
    EXPECT_TRUE(isa<CallInst>(firstInstruction))
        << "Verify If The Fisrt Instruction of 'main' function is a CallInst\n";  
    }
}
