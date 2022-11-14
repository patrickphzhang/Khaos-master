add_llvm_library( LLVMCodeProtMid
  Utils.cpp
  ParseJson.cpp
  BogusControlFlow.cpp
  Flattening.cpp
  Substitution.cpp 
  Fus.cpp
  InterFunctionPrepare.cpp
  InterFunctionShuffleBlock.cpp
  InterFunctionShuffleLoop.cpp
  InterFunctionShufflePosition.cpp
  KhaosCodeExtractor.cpp
  CryptoUtils.cpp
  SplitBasicBlocks.cpp
  HarmnessAnalysis.cpp
  InterFunctionDeepFusionPrepare.cpp
  InterFunctionShuffleOpt.cpp
)

add_dependencies(LLVMCodeProtMid intrinsics_gen)
