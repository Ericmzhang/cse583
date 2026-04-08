//==- CFLAndersAliasAnalysis.h - Unification-based Alias Analysis -*- C++-*-==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
/// This is the interface for LLVM's inclusion-based alias analysis
/// implemented with CFL graph reachability.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_CFLANDERSTAINTANALYSIS_H
#define LLVM_ANALYSIS_CFLANDERSTAINTANALYSIS_H

#include "AliasAnalysisSummary.h"
#include "CFLTaintAnalysisUtils.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Optional.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include <forward_list>
#include <memory>

namespace llvm {

class Function;
class MemoryLocation;
class TargetLibraryInfo;

class CFLAndersTaintResult : public AAResultBase<CFLAndersTaintResult> {
  friend AAResultBase<CFLAndersTaintResult>;

  class FunctionInfo;

public:
  explicit CFLAndersTaintResult(const TargetLibraryInfo &TLI);
  CFLAndersTaintResult(CFLAndersTaintResult &&RHS);
  ~CFLAndersTaintResult();

  Optional<DenseSet<Value *>> taintedVals(const Function &Fn);
  DenseMap<const Function *, DenseSet<Value *>> taintedValsInReachableFuncs(const Function &Fn);
  void buildInfoFrom(const Module &);

private:
  const TargetLibraryInfo &TLI;

  /// Cached mapping of Functions to their StratifiedSets.
  /// If a function's sets are currently being built, it is marked
  /// in the cache as an Optional without a value. This way, if we
  /// have any kind of recursion, it is discernable from a function
  /// that simply has empty sets.
  
  DenseMap<const Function *, DenseSet<Value *>> TaintedValMap; 
};

/// Analysis pass providing a never-invalidated alias analysis result.
///
/// FIXME: We really should refactor CFL to use the analysis more heavily, and
/// in particular to leverage invalidation to trigger re-computation.
class CFLAndersAA : public AnalysisInfoMixin<CFLAndersAA> {
  friend AnalysisInfoMixin<CFLAndersAA>;

  static AnalysisKey Key;

public:
  using Result = CFLAndersTaintResult;

  CFLAndersTaintResult run(Function &F, FunctionAnalysisManager &AM);
};

/// Legacy wrapper pass to provide the CFLAndersTaintResult object.
class CFLAndersTaintWrapperPass : public ModulePass {
  std::unique_ptr<CFLAndersTaintResult> Result;
  
public:
  static char ID;

  CFLAndersTaintWrapperPass(); 
  CFLAndersTaintResult &getResult() { return *Result; }
  const CFLAndersTaintResult &getResult() const { return *Result; }
 
  bool runOnModule(Module &M);
  //void initializePass() override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
};

ModulePass *createCFLAndersTaintWrapperPass();

} // end namespace llvm

#endif 
