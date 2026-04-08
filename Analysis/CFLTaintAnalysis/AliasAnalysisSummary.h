//=====- CFLSummary.h - Abstract stratified sets implementation. --------=====//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
/// This file defines various utility types and functions useful to
/// summary-based alias analysis.
///
/// Summary-based analysis, also known as bottom-up analysis, is a style of
/// interprocedrual static analysis that tries to analyze the callees before the
/// callers get analyzed. The key idea of summary-based analysis is to first
/// process each function independently, outline its behavior in a condensed
/// summary, and then instantiate the summary at the callsite when the said
/// function is called elsewhere. This is often in contrast to another style
/// called top-down analysis, in which callers are always analyzed first before
/// the callees.
///
/// In a summary-based analysis, functions must be examined independently and
/// out-of-context. We have no information on the state of the memory, the
/// arguments, the global values, and anything else external to the function. To
/// carry out the analysis conservative assumptions have to be made about those
/// external states. In exchange for the potential loss of precision, the
/// summary we obtain this way is highly reusable, which makes the analysis
/// easier to scale to large programs even if carried out context-sensitively.
///
/// Currently, all CFL-based alias analyses adopt the summary-based approach
/// and therefore heavily rely on this header.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_TAINT_ALIASANALYSISSUMMARY_H
#define LLVM_ANALYSIS_TAINT_ALIASANALYSISSUMMARY_H
#include "llvm/ADT/DenseMapInfo.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/DataLayout.h" 
#include "llvm/IR/Operator.h"
#include <bitset>
#include <variant>

namespace llvm {
namespace cflta {

//===----------------------------------------------------------------------===//
// MatchState related stuffs
//===----------------------------------------------------------------------===//

enum class MatchState : uint8_t {
  // The following state represents S1 in the paper.
  FlowFromReadOnly = 0,
  // The following two states together represent S2 in the paper.
  // The 'NoReadWrite' suffix indicates that there exists an alias path that
  // does not contain assignment and reverse assignment edges.
  // The 'ReadOnly' suffix indicates that there exists an alias path that
  // contains reverse assignment edges only.
  FlowFromMemAliasNoReadWrite,
  FlowFromMemAliasReadOnly,
  // The following two states together represent S3 in the paper.
  // The 'WriteOnly' suffix indicates that there exists an alias path that
  // contains assignment edges only.
  // The 'ReadWrite' suffix indicates that there exists an alias path that
  // contains both assignment and reverse assignment edges. Note that if X and Y
  // are reachable at 'ReadWrite' state, it does NOT mean X is both read from
  // and written to Y. Instead, it means that a third value Z is written to both
  // X and Y.
  FlowToWriteOnly,
  FlowToReadWrite,
  // The following two states together represent S4 in the paper.
  FlowToMemAliasWriteOnly,
  FlowToMemAliasReadWrite,
};

using StateSet = std::bitset<7>;

static inline StateSet toStateSet(MatchState State) {
  return StateSet(1U << static_cast<uint8_t>(State));
}
//===----------------------------------------------------------------------===//
// AliasAttr related stuffs
//===----------------------------------------------------------------------===//

/// The number of attributes that AliasAttr should contain. Attributes are
/// described below, and 32 was an arbitrary choice because it fits nicely in 32
/// bits (because we use a bitset for AliasAttr).
static const unsigned NumAliasAttrs = 32;

/// These are attributes that an alias analysis can use to mark certain special
/// properties of a given pointer. Refer to the related functions below to see
/// what kinds of attributes are currently defined.
typedef std::bitset<NumAliasAttrs> AliasAttrs;

/// Attr represent whether the said pointer comes from an unknown source
/// (such as opaque memory or an integer cast).
AliasAttrs getAttrNone();

/// AttrUnknown represent whether the said pointer comes from a source not known
/// to alias analyses (such as opaque memory or an integer cast).
AliasAttrs getAttrUnknown();
bool hasUnknownAttr(AliasAttrs);

/// AttrCaller represent whether the said pointer comes from a source not known
/// to the current function but known to the caller. Values pointed to by the
/// arguments of the current function have this attribute set
AliasAttrs getAttrCaller();
bool hasCallerAttr(AliasAttrs);
bool hasUnknownOrCallerAttr(AliasAttrs);

/// AttrEscaped represent whether the said pointer comes from a known source but
/// escapes to the unknown world (e.g. casted to an integer, or passed as an
/// argument to opaque function). Unlike non-escaped pointers, escaped ones may
/// alias pointers coming from unknown sources.
AliasAttrs getAttrEscaped();
bool hasEscapedAttr(AliasAttrs);

/// AttrGlobal represent whether the said pointer is a global value.
/// AttrArg represent whether the said pointer is an argument, and if so, what
/// index the argument has.
AliasAttrs getGlobalOrArgAttrFromValue(const Value &);
bool isGlobalOrArgAttr(AliasAttrs);
bool hasGlobalAttr(AliasAttrs); 

/// Given an AliasAttrs, return a new AliasAttrs that only contains attributes
/// meaningful to the caller. This function is primarily used for
/// interprocedural analysis
/// Currently, externally visible AliasAttrs include AttrUnknown, AttrGlobal,
/// and AttrEscaped
AliasAttrs getExternallyVisibleAttrs(AliasAttrs);

//===----------------------------------------------------------------------===//
// Function summary related stuffs
//===----------------------------------------------------------------------===//

/// The maximum number of arguments we can put into a summary.
static const unsigned MaxSupportedArgsInSummary = 50;

/// We use InterfaceValue to describe parameters/return value, as well as
/// potential memory locations that are pointed to by parameters/return value,
/// of a function.
/// Index is an integer which represents a single parameter or a return value.
/// When the index is 0, it refers to the return value. Non-zero index i refers
/// to the i-th parameter.
/// DerefLevel indicates the number of dereferences one must perform on the
/// parameter/return value to get this InterfaceValue.
struct InterfaceValue {
  unsigned Index;
  unsigned DerefLevel;
};

inline bool operator==(InterfaceValue LHS, InterfaceValue RHS) {
  return LHS.Index == RHS.Index && LHS.DerefLevel == RHS.DerefLevel;
}
inline bool operator!=(InterfaceValue LHS, InterfaceValue RHS) {
  return !(LHS == RHS);
}
inline bool operator<(InterfaceValue LHS, InterfaceValue RHS) {
  return LHS.Index < RHS.Index ||
         (LHS.Index == RHS.Index && LHS.DerefLevel < RHS.DerefLevel);
}
inline bool operator>(InterfaceValue LHS, InterfaceValue RHS) {
  return RHS < LHS;
}
inline bool operator<=(InterfaceValue LHS, InterfaceValue RHS) {
  return !(RHS < LHS);
}
inline bool operator>=(InterfaceValue LHS, InterfaceValue RHS) {
  return !(LHS < RHS);
}
inline raw_ostream &operator<<(raw_ostream &OS, const InterfaceValue &IV) {
    return OS << "interface value " << IV.Index << " at level " << IV.DerefLevel;
}

// We use UnknownOffset to represent pointer offsets that cannot be determined
// at compile time. Note that MemoryLocation::UnknownSize cannot be used here
// because we require a signed value.
static const int64_t UnknownOffset = INT64_MAX;

inline int64_t addOffset(int64_t LHS, int64_t RHS) {
  if (LHS == UnknownOffset || RHS == UnknownOffset)
    return UnknownOffset;
  // FIXME: Do we need to guard against integer overflow here?
  return LHS + RHS;
}

static uint64_t getGEPOffset(const GEPOperator &GEPOp, const DataLayout &DL) {
  uint64_t Offset = UnknownOffset;
  APInt APOffset(DL.getPointerSizeInBits(GEPOp.getPointerAddressSpace()), 0);
  if (GEPOp.accumulateConstantOffset(DL, APOffset) && APOffset.getSExtValue() >= 0)
    Offset = APOffset.getSExtValue();
  return Offset;
}

/// We use ExternalRelation to describe an externally visible aliasing relations
/// between parameters/return value of a function.
struct ExternalRelation {
  InterfaceValue From, To;
  int64_t Offset;
};

inline bool operator==(ExternalRelation LHS, ExternalRelation RHS) {
  return LHS.From == RHS.From && LHS.To == RHS.To && LHS.Offset == RHS.Offset;
}
inline bool operator!=(ExternalRelation LHS, ExternalRelation RHS) {
  return !(LHS == RHS);
}
inline bool operator<(ExternalRelation LHS, ExternalRelation RHS) {
  if (LHS.From < RHS.From)
    return true;
  if (LHS.From > RHS.From)
    return false;
  if (LHS.To < RHS.To)
    return true;
  if (LHS.To > RHS.To)
    return false;
  return LHS.Offset < RHS.Offset;
}
inline bool operator>(ExternalRelation LHS, ExternalRelation RHS) {
  return RHS < LHS;
}
inline bool operator<=(ExternalRelation LHS, ExternalRelation RHS) {
  return !(RHS < LHS);
}
inline bool operator>=(ExternalRelation LHS, ExternalRelation RHS) {
  return !(LHS < RHS);
}

/// We use ExternalAttribute to describe an externally visible AliasAttrs
/// for parameters/return value.
struct ExternalAttribute {
  InterfaceValue IValue;
  AliasAttrs Attr;
};

/// We use ExternalAttribute to describe an externally visible taint
/// for parameters/return value.
struct ExternalTaint {
  InterfaceValue IValue;
  StateSet TaintStates;
};

/// AliasSummary is just a collection of ExternalRelation and ExternalAttribute
struct AliasSummary {
  // RetParamRelations is a collection of ExternalRelations.
  SmallVector<ExternalRelation, 8> RetParamRelations;

  // RetParamAttributes is a collection of ExternalAttributes.
  SmallVector<ExternalAttribute, 8> RetParamAttributes;
  
  // RetParamTaints is a collection of ExternalTaints.
  SmallVector<ExternalTaint, 8> RetParamTaints;
};

/// This is the result of instantiating InterfaceValue at a particular callsite
struct InstantiatedValue {
  Value *Val;
  unsigned DerefLevel;
};
Optional<InstantiatedValue> instantiateInterfaceValue(InterfaceValue, CallSite);

inline bool operator==(InstantiatedValue LHS, InstantiatedValue RHS) {
  return LHS.Val == RHS.Val && LHS.DerefLevel == RHS.DerefLevel;
}
inline bool operator!=(InstantiatedValue LHS, InstantiatedValue RHS) {
  return !(LHS == RHS);
}
inline bool operator<(InstantiatedValue LHS, InstantiatedValue RHS) {
  return std::less<Value *>()(LHS.Val, RHS.Val) ||
         (LHS.Val == RHS.Val && LHS.DerefLevel < RHS.DerefLevel);
}
inline bool operator>(InstantiatedValue LHS, InstantiatedValue RHS) {
  return RHS < LHS;
}
inline bool operator<=(InstantiatedValue LHS, InstantiatedValue RHS) {
  return !(RHS < LHS);
}
inline bool operator>=(InstantiatedValue LHS, InstantiatedValue RHS) {
  return !(LHS < RHS);
}
inline raw_ostream &operator<<(raw_ostream &OS, const InstantiatedValue &IV) {
    return OS << *IV.Val << " at level " << IV.DerefLevel;
}

class TaintedSet: public DenseMap<InstantiatedValue, StateSet> {
public:
  StateSet addStates(InstantiatedValue IVal, StateSet NewStates);
};  

using FuncTaintMap = DenseMap<const Function *, cflta::TaintedSet>;

struct InterprocTaintInfo {
  //Save all tainted globals
  TaintedSet TaintedGlobalVars;
  
  //Save for each function all formal arguments and globals tainted
  FuncTaintMap TaintedFuncArgsGlobals; 
};

/// This is the result of instantiating ExternalRelation at a particular
/// callsite
struct InstantiatedRelation {
  InstantiatedValue From, To;
  int64_t Offset;
};
Optional<InstantiatedRelation> instantiateExternalRelation(ExternalRelation, CallSite);

/// This is the result of instantiating ExternalAttribute at a particular
/// callsite
struct InstantiatedAttr {
  InstantiatedValue IValue;
  AliasAttrs Attr;
};
Optional<InstantiatedAttr> instantiateExternalAttribute(ExternalAttribute, CallSite);

struct InstantiatedTaint {
  InstantiatedValue IValue;
  StateSet TaintStates;
};
Optional<InstantiatedTaint> instantiateExternalTaint(ExternalTaint, CallSite);
}

template <> struct DenseMapInfo<cflta::InstantiatedValue> {
  static inline cflta::InstantiatedValue getEmptyKey() {
    return cflta::InstantiatedValue{DenseMapInfo<Value *>::getEmptyKey(),
                                    DenseMapInfo<unsigned>::getEmptyKey()};
  }
  static inline cflta::InstantiatedValue getTombstoneKey() {
    return cflta::InstantiatedValue{DenseMapInfo<Value *>::getTombstoneKey(),
                                    DenseMapInfo<unsigned>::getTombstoneKey()};
  }
  static unsigned getHashValue(const cflta::InstantiatedValue &IV) {
    return DenseMapInfo<std::pair<Value *, unsigned>>::getHashValue(
        std::make_pair(IV.Val, IV.DerefLevel));
  }
  static bool isEqual(const cflta::InstantiatedValue &LHS,
                      const cflta::InstantiatedValue &RHS) {
    return LHS.Val == RHS.Val && LHS.DerefLevel == RHS.DerefLevel;
  }
};
}

#endif
