cmake_minimum_required(VERSION 3.10)
project(PMRobustness)

find_package(LLVM REQUIRED CONFIG)

list(APPEND CMAKE_MODULE_PATH ${LLVM_CMAKE_DIR})
include(AddLLVM)

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
include_directories(${CMAKE_CURRENT_SOURCE_DIR})

# 1. Include the necessary LLVM components
set(LLVM_LINK_COMPONENTS 
    Core 
    Support 
    Analysis 
    TransformUtils 
    InstCombine
    ScalarOpts
)

# 2. Add the library
add_llvm_library(libPMRobustness MODULE BUILDTREE_ONLY
  PMRobustness.cpp
  ../Analysis/CFLTaintAnalysis/CFLAndersTaintAnalysis.cpp
  ../Analysis/CFLTaintAnalysis/CFLGraph.cpp 
  ../Analysis/CFLTaintAnalysis/AliasAnalysisSummary.cpp  
  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
)

# 3. Use the PRIVATE keyword to match LLVM's internal style
llvm_map_components_to_libnames(llvm_libs Analysis Core Support TransformUtils)

target_link_libraries(libPMRobustness PRIVATE ${llvm_libs})