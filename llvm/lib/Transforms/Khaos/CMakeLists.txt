add_llvm_library( LLVMKhaosMid
  Utils.cpp
  ParseJson.cpp
  BogusControlFlow.cpp
  Flattening.cpp
  Substitution.cpp 
  Fus.cpp
  InterFunctionPrepare.cpp
  InterFunctionShufflePosition.cpp
  KhaosCodeExtractor.cpp
  CryptoUtils.cpp
  SplitBasicBlocks.cpp
  HarmnessAnalysis.cpp
  InterFunctionDeepFusionPrepare.cpp
  InterFunctionShuffleOpt.cpp
)

add_dependencies(LLVMKhaosMid intrinsics_gen)
