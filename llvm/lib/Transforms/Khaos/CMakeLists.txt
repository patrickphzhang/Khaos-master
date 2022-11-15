add_llvm_library( LLVMKhaosMid
  Utils.cpp
  ParseJson.cpp
  BogusControlFlow.cpp
  Flattening.cpp
  Substitution.cpp 
  Fus.cpp
  FusPrepare.cpp
  FisPosition.cpp
  KhaosCodeExtractor.cpp
  CryptoUtils.cpp
  HarmnessAnalysis.cpp
  DeepFusionPrepare.cpp
  Fis.cpp
)

add_dependencies(LLVMKhaosMid intrinsics_gen)
