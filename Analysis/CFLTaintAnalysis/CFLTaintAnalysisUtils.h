//=- CFLTaintAnalysisUtils.h - Utilities for CFL Alias Analysis ----*- C++-*-=//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
// \file
// These are the utilities/helpers used by the CFL Taint Analyses
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_CFLTAINTANALYSISUTILS_H
#define LLVM_ANALYSIS_CFLTAINTANALYSISUTILS_H

#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/ValueHandle.h"

#include <cxxabi.h>

namespace llvm {
namespace cflta {

template <typename AAResult> struct FunctionHandle final : public CallbackVH {
  FunctionHandle(Function *Fn, AAResult *Result)
      : CallbackVH(Fn), Result(Result) {
    assert(Fn != nullptr);
    assert(Result != nullptr);
  }

  void deleted() override { removeSelfFromCache(); }
  void allUsesReplacedWith(Value *) override { removeSelfFromCache(); }

private:
  AAResult *Result;

  void removeSelfFromCache() {
    assert(Result != nullptr);
    auto *Val = getValPtr();
    Result->evict(cast<Function>(Val));
    setValPtr(nullptr);
  }
};

static inline const Function *parentFunctionOfValue(const Value *Val) {
  if (auto *Inst = dyn_cast<Instruction>(Val)) {
    return Inst->getFunction();
  }

  if (auto *Arg = dyn_cast<Argument>(Val))
    return Arg->getParent();
  return nullptr;
}

static inline unsigned maxDerefLevel(const Value* V) {
  DenseSet<const StructType *> Seen;
  auto T = V->getType();
  std::function<unsigned(const Type *)> getLevel = [&] (const Type *T) {
    unsigned Max = 0;
    auto ArType = dyn_cast<ArrayType>(T);
    auto PtrType = dyn_cast<PointerType>(T);
    for (; PtrType || ArType; ArType = dyn_cast<ArrayType>(T), PtrType = dyn_cast<PointerType>(T)) {
     if(PtrType) {
       Max++;
  	   T = PtrType->getPointerElementType();
     } else {
       T = ArType->getElementType();
	 }
    }
    if (auto StrType = dyn_cast<StructType>(T)) {
      if (Seen.insert(StrType).second) {
        unsigned ChildMax = 0;
        for (auto Element: StrType->elements()) {
 		  ChildMax = std::max(ChildMax, getLevel(Element));
        }
        Max += ChildMax;
      }
    }
    return Max;
  };
  return getLevel(T); 
}

static inline bool isValueImmutable(const Value *V) {
	if(auto GV = dyn_cast<GlobalVariable>(V))
		return GV->isConstant();
    return isa<Constant>(V);
}

static inline StringRef getDemangledName(const Function& Fn) {
  auto FName = Fn.getName();
  int status;
  auto demangled = abi::__cxa_demangle(FName.begin(), 0, 0, &status);
  if (status==0) {
    FName = demangled;
  }
  return FName;
}

} // namespace llvm
}

#endif // LLVM_ANALYSIS_CFLALIASANALYSISUTILS_H
