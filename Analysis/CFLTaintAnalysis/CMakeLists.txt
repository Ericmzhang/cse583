if(WIN32 OR CYGWIN)
  set(LLVM_LINK_COMPONENTS Core Support)
endif()

add_llvm_library(libCFLTaintAnalysis MODULE BUILDTREE_ONLY
  CFLAndersTaintAnalysis.cpp
  AliasAnalysisSummary.cpp
  CFLGraph.cpp

  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
  )
