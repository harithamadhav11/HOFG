add_llvm_component_library(LLVMHOFG
  HOFG.cpp

  DEPENDS
  intrinsics_gen

  LINK_COMPONENTS
  Core
  Support
  )
