add_llvm_library( LLVMKhaosMid
  Utils.cpp
  Fus.cpp
  FisPosition.cpp
  KhaosCodeExtractor.cpp
  Fis.cpp
  Hid.cpp
  Cat.cpp
  AutoMode.cpp
  StripSkippedFunctions.cpp
)

add_dependencies(LLVMKhaosMid intrinsics_gen)
