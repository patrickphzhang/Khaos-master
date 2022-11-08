set(LLVM_LINK_COMPONENTS
  Analysis
  AsmParser
  Core
  Support
  TransformUtils
  CodeProtMid
  )

add_llvm_unittest(CodeProtTests
    AntiDumpTest.cpp
  )
