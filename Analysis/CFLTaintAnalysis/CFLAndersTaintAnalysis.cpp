//===- CFLAndersAliasAnalysis.cpp - Unification-based Alias Analysis ------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements a CFL-based, summary-based alias analysis algorithm. It
// differs from CFLSteensAliasAnalysis in its inclusion-based nature while
// CFLSteensAliasAnalysis is unification-based. This pass has worse performance
// than CFLSteensAliasAnalysis (the worst case complexity of
// CFLAndersAliasAnalysis is cubic, while the worst case complexity of
// CFLSteensAliasAnalysis is almost linear), but it is able to yield more
// precise analysis result. The precision of this analysis is roughly the same
// as that of an one level context-sensitive Andersen's algorithm.
//
// The algorithm used here is based on recursive state machine matching scheme
// proposed in "Demand-driven alias analysis for C" by Xin Zheng and Radu
// Rugina. The general idea is to extend the traditional transitive closure
// algorithm to perform CFL matching along the way: instead of recording
// "whether X is reachable from Y", we keep track of "whether X is reachable
// from Y at state Z", where the "state" field indicates where we are in the CFL
// matching process. To understand the matching better, it is advisable to have
// the state machine shown in Figure 3 of the paper available when reading the
// codes: all we do here is to selectively expand the transitive closure by
// discarding edges that are not recognized by the state machine.
//
// There are two differences between our current implementation and the one
// described in the paper:
// - Our algorithm eagerly computes all alias pairs after the CFLGraph is built,
// while in the paper the authors did the computation in a demand-driven
// fashion. We did not implement the demand-driven algorithm due to the
// additional coding complexity and higher memory profile, but if we found it
// necessary we may switch to it eventually.
// - In the paper the authors use a state machine that does not distinguish
// value reads from value writes. For example, if Y is reachable from X at state
// S3, it may be the case that X is written into Y, or it may be the case that
// there's a third value Z that writes into both X and Y. To make that
// distinction (which is crucial in building function summary as well as
// retrieving mod-ref info), we choose to duplicate some of the states in the
// paper's proposed tate machine. The duplication does not change the set the
// machine accepts. Given a pair of reachable values, it only provides more
// detailed information on which value is being written into and which is being
// read from.
//
//===----------------------------------------------------------------------===//

// N.B. AliasAnalysis as a whole is phrased as a FunctionPass at the moment, and
// CFLAndersAA is interprocedural. This is *technically* A Bad Thing, because
// FunctionPasses are only allowed to inspect the Function that they're being
// run on. Realistically, this likely isn't a problem until we allow
// FunctionPasses to run concurrently.

#include "CFLAndersTaintAnalysis.h"
#include "AliasAnalysisSummary.h"
#include "CFLGraph.h"
#include "CFLTaintAnalysisUtils.h"
#include "CFLGraphBuilder.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseMapInfo.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/None.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include <algorithm>
#include <bitset>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <utility>
#include <vector>

using namespace llvm;
using namespace llvm::cflta;

#define DEBUG_TYPE "cfl-anders-taint"

CFLAndersTaintResult::CFLAndersTaintResult(const TargetLibraryInfo &TLI) : TLI(TLI) {}
CFLAndersTaintResult::CFLAndersTaintResult(CFLAndersTaintResult &&RHS)
    : AAResultBase(std::move(RHS)), TLI(RHS.TLI) {}
CFLAndersTaintResult::~CFLAndersTaintResult() = default;

namespace {

const unsigned ReadOnlyStateMask =
    (1U << static_cast<uint8_t>(MatchState::FlowFromReadOnly)) |
    (1U << static_cast<uint8_t>(MatchState::FlowFromMemAliasReadOnly));
const unsigned WriteOnlyStateMask =
    (1U << static_cast<uint8_t>(MatchState::FlowToWriteOnly)) |
    (1U << static_cast<uint8_t>(MatchState::FlowToMemAliasWriteOnly));
const unsigned ReadWriteStateMask =
    (1U << static_cast<uint8_t>(MatchState::FlowToReadWrite)) |
    (1U << static_cast<uint8_t>(MatchState::FlowToMemAliasReadWrite));
const unsigned ReadStateMask =
    ReadOnlyStateMask | ReadWriteStateMask;    
const unsigned WriteStateMask =
    WriteOnlyStateMask | ReadWriteStateMask;    
const unsigned MemStateMask =
    (1U << static_cast<uint8_t>(MatchState::FlowFromMemAliasNoReadWrite)) |
    (1U << static_cast<uint8_t>(MatchState::FlowToMemAliasReadWrite)) |
    (1U << static_cast<uint8_t>(MatchState::FlowToMemAliasWriteOnly)) |
    (1U << static_cast<uint8_t>(MatchState::FlowFromMemAliasReadOnly));


static inline bool hasReadOnlyState(StateSet Set) {
  return (Set & StateSet(ReadOnlyStateMask)).any();
}

static inline bool hasWriteOnlyState(StateSet Set) {
  return (Set & StateSet(WriteOnlyStateMask)).any();
}

static inline bool hasReadWriteState(StateSet Set) {
  return (Set & StateSet(ReadWriteStateMask)).any();
}

static inline bool hasWriteState(StateSet Set) {
  return (Set & StateSet(WriteStateMask)).any();
}

static inline bool hasReadState(StateSet Set) {
  return (Set & StateSet(ReadStateMask)).any();
}

static inline bool hasNonWriteState(StateSet Set) {
  return (Set & ~StateSet(WriteStateMask)).any();
}

static inline bool hasNonReadState(StateSet Set) {
  return (Set & ~StateSet(ReadStateMask)).any();
}

static inline bool hasNonReadOnlyState(StateSet Set) {
  return (Set & ~StateSet(ReadOnlyStateMask)).any();
}

static inline bool hasNonMemAliasState(StateSet Set) {
  return (Set & ~StateSet(MemStateMask)).any();
}

static inline bool hasMemAliasWriteState(StateSet Set) {
  return (Set & StateSet(MemStateMask) & StateSet(WriteStateMask)).any();
}

static inline bool hasMemAliasNonWriteState(StateSet Set) {
  return (Set & StateSet(MemStateMask) & ~StateSet(WriteStateMask)).any();
}

static bool hasMemAliasNonReadState(StateSet Set) {
  return (Set & StateSet(MemStateMask) & ~StateSet(ReadStateMask)).any();
}

static const std::string StateNames[] = { "FlowFromReadOnly", "FlowFromMemAliasNoReadWrite", "FlowFromMemAliasReadOnly", "FlowToWriteOnly", "FlowToReadWrite", "FlowToMemAliasWriteOnly", "FlowToMemAliasReadWrite" };

raw_ostream &operator << ( raw_ostream& strm, MatchState ms )
{
   return strm << StateNames[(int)ms];
}

static inline Optional<MatchState> applyRead(MatchState State) {
  if(hasNonWriteState(toStateSet(State)))
    return MatchState::FlowFromReadOnly;
  return None;
}

static inline MatchState applyWrite(MatchState State) {
  if(hasReadState(toStateSet(State)))
    return MatchState::FlowToReadWrite;
  else
    return MatchState::FlowToWriteOnly;
}

static inline Optional<MatchState> applyMemAlias(MatchState State) {
  switch (State) {
    case MatchState::FlowFromReadOnly:
      return MatchState::FlowFromMemAliasReadOnly;
    case MatchState::FlowToWriteOnly:
      return MatchState::FlowToMemAliasWriteOnly;
    case MatchState::FlowToReadWrite:
      return MatchState::FlowToMemAliasReadWrite;
    default:
      return None;
  }
}

static inline StateSet composeStateSets(StateSet First, StateSet Second) {
   StateSet Res;

   if (hasNonWriteState(First) && Second.test(static_cast<uint8_t>(MatchState::FlowFromReadOnly)))
     Res.set(static_cast<uint8_t>(MatchState::FlowFromReadOnly));

   if (hasNonReadState(First) && Second.test(static_cast<uint8_t>(MatchState::FlowToWriteOnly)))
     Res.set(static_cast<uint8_t>(MatchState::FlowToWriteOnly));

   if ((hasReadState(First) && Second.test(static_cast<uint8_t>(MatchState::FlowToWriteOnly))) ||
       (hasReadOnlyState(First) && Second.test(static_cast<uint8_t>(MatchState::FlowToReadWrite))))
     Res.set(static_cast<uint8_t>(MatchState::FlowToReadWrite));

   if (First.test(static_cast<uint8_t>(MatchState::FlowFromReadOnly)) && hasMemAliasNonWriteState(Second))
     Res.set(static_cast<uint8_t>(MatchState::FlowFromMemAliasReadOnly));

   if (First.test(static_cast<uint8_t>(MatchState::FlowToWriteOnly)) && hasMemAliasNonReadState(Second))
     Res.set(static_cast<uint8_t>(MatchState::FlowToMemAliasWriteOnly));

   if ((First.test(static_cast<uint8_t>(MatchState::FlowFromReadOnly)) && hasMemAliasWriteState(Second)) ||
       (First.test(static_cast<uint8_t>(MatchState::FlowToReadWrite)) && hasMemAliasNonReadState(Second)))
     Res.set(static_cast<uint8_t>(MatchState::FlowToMemAliasReadWrite));

   return Res;
}

//===----------------------------------------------------------------------===//
// CallContext related stuff
//===----------------------------------------------------------------------===//
enum CallContext: uint8_t
{
  Call,
  Return,
  ReturnCall,
  Normal,
};

using ContextSet = std::bitset<3>;

static inline ContextSet toContextSet (CallContext Context) {
  return ContextSet(1U << static_cast<uint8_t>(Context));
}

static inline Optional<CallContext> composeCallContexts (CallContext First, CallContext Second) {
  if (First == CallContext::Normal)
    return Second;
  if (Second == CallContext::Normal)
    return First;
  if (First == CallContext::Call && Second == CallContext::Call)
    return First;
  if (First == CallContext::Return && Second == CallContext::Return)
    return First;
  if (First == CallContext::Return && Second == CallContext::ReturnCall)
    return Second;
  return None;
}

static inline ContextSet composeContextSets(ContextSet First, ContextSet Second) {
   ContextSet Res;

   if (First.test(static_cast<uint8_t>(CallContext::Normal)))
     Res &= Second;
   if (Second.test(static_cast<uint8_t>(CallContext::Normal)))
     Res &= First;
   if (First.test(static_cast<uint8_t>(CallContext::Call)) && Second.test(static_cast<uint8_t>(CallContext::Call)))
     Res.set(CallContext::Call);
   if (First.test(static_cast<uint8_t>(CallContext::Return)) && Second.test(static_cast<uint8_t>(CallContext::Return)))
     Res.set(CallContext::Return);
   if ((First.test(static_cast<uint8_t>(CallContext::Return)) && Second.test(static_cast<uint8_t>(CallContext::Call))) || 
       (First.test(static_cast<uint8_t>(CallContext::ReturnCall)) && Second.test(static_cast<uint8_t>(CallContext::Call))) || 	   
       (First.test(static_cast<uint8_t>(CallContext::Return)) && Second.test(static_cast<uint8_t>(CallContext::ReturnCall))))
     Res.set(CallContext::ReturnCall);

   return Res;
}

template<typename T>
class ContextMap {
  static const uint8_t EnumSize = 4;
  T Map[EnumSize];
public:
  class const_iterator {
    uint8_t ContextInt;
    const T *Value;
    
  public:
    const_iterator(uint8_t ContextInt, const T *Value): ContextInt(ContextInt), Value(Value) {}
    const_iterator() = default;

    std::pair<CallContext, T> operator*() {
      return std::make_pair(CallContext(ContextInt), *Value);
    }

    bool operator==(const_iterator Other) {
      return Value == Other.Value && ContextInt == Other.ContextInt;
    }

    bool operator!=(const_iterator Other) {
      return !(*this == Other);
    }

    const_iterator operator++() {
      ContextInt++;
      Value++;
      return *this;
    }
  };

  T &operator[] (CallContext Context) {
    return Map[static_cast<uint8_t>(Context)];
  }

  const_iterator begin() const {
    return const_iterator(0, &Map[0]);
  }

  const_iterator end() const {
    return const_iterator(EnumSize, &Map[EnumSize]);
  }
};

// A pair that consists of a value and an offset
struct OffsetValue {
  const Value *Val;
  int64_t Offset;
};

bool operator==(OffsetValue LHS, OffsetValue RHS) {
  return LHS.Val == RHS.Val && LHS.Offset == RHS.Offset;
}

bool operator<(OffsetValue LHS, OffsetValue RHS) {
  return std::less<const Value *>()(LHS.Val, RHS.Val) ||
         (LHS.Val == RHS.Val && LHS.Offset < RHS.Offset);
}

inline raw_ostream &operator<<(raw_ostream &OS, const OffsetValue &OV) {
    return OS << *OV.Val << " at offset " << OV.Offset;
}
// A pair that consists of an InstantiatedValue and an offset
struct OffsetInstantiatedValue {
  InstantiatedValue IVal;
  int64_t Offset;
};

bool operator==(OffsetInstantiatedValue LHS, OffsetInstantiatedValue RHS) {
  return LHS.IVal == RHS.IVal && LHS.Offset == RHS.Offset;
}

inline raw_ostream &operator<<(raw_ostream &OS, const OffsetInstantiatedValue &OIV) {
    return OS << OIV.IVal << " offset " << OIV.Offset;
}

// We use ReachabilitySet to keep track of value aliases (The nonterminal "V" in
// the paper) during the analysis.
using ValueStateMap = DenseMap<InstantiatedValue, StateSet>;

class ValueReachMap : public DenseMap<InstantiatedValue, ValueStateMap> {
public:
  iterator_range<ValueStateMap::const_iterator>
  reachableValueAliases(InstantiatedValue V) const {
    auto Itr = find(V);
    if (Itr == end()) {
      return make_range<ValueStateMap::const_iterator>(ValueStateMap::const_iterator(),
                                                       ValueStateMap::const_iterator());
	}
    return make_range<ValueStateMap::const_iterator>(Itr->second.begin(),
                                                 Itr->second.end());
  }
};

class ReachabilitySet {
  // the set of all ('From', 'State') tuples for a given node 'To'
  ValueReachMap RevReachMap;
  // the set of all ('To', 'State') tuples for a given node 'From'
  ValueReachMap ReachMap;
public:
  using const_value_iterator = ValueReachMap::const_iterator;

  // Insert edge 'From->To' at state 'State'
  bool insert(InstantiatedValue From, InstantiatedValue To, MatchState State) {
    //assert(From != To);
    auto &RevStates = RevReachMap[To][From];
    auto &States = ReachMap[From][To];
    auto Idx = static_cast<size_t>(State);
    if (!RevStates.test(Idx)) {
      RevStates.set(Idx);
	  States.set(Idx);
      return true;
    }
    return false;
  }

  bool insertStates(InstantiatedValue From, InstantiatedValue To, StateSet NewStates) {
    //assert(From != To);
    auto &RevStates = RevReachMap[To][From];
    auto &States = ReachMap[From][To];
    if ((~RevStates & NewStates).any()) {
      RevStates |= NewStates;
	  States |= NewStates;
      return true;
    }
    return false;
  }

  iterator_range<const_value_iterator> value_mappings() const {
    return make_range<const_value_iterator>(RevReachMap.begin(), RevReachMap.end());
  }

  ValueReachMap getReachMap() const {
    return ReachMap;
  }
  
  ValueReachMap getRevReachMap() const {
    return RevReachMap;
  }
};

// We use AliasMemSet to keep track of all memory aliases (the nonterminal "M"
// in the paper) during the analysis.
class AliasMemSet {
  using MemSet = DenseSet<InstantiatedValue>;
  using MemMapType = DenseMap<InstantiatedValue, MemSet>;

  MemMapType MemMap;

public:
  using const_mem_iterator = MemSet::const_iterator;

  bool insert(InstantiatedValue LHS, InstantiatedValue RHS) {
    // Top-level values can never be memory aliases because one cannot take the
    // addresses of them
    //assert(LHS.DerefLevel > 0 && RHS.DerefLevel > 0);
    return MemMap[LHS].insert(RHS).second;
  }

  const MemSet *getMemoryAliases(InstantiatedValue V) const {
    auto Itr = MemMap.find(V);
    if (Itr == MemMap.end())
      return nullptr;
    return &Itr->second;
  }
};

// We use AliasAttrMap to keep track of the AliasAttr of each node.
class AliasAttrMap {
  using MapType = DenseMap<InstantiatedValue, AliasAttrs>;

  MapType AttrMap;

public:
  using const_iterator = MapType::const_iterator;

  bool add(InstantiatedValue V, AliasAttrs Attr) {
    auto &OldAttr = AttrMap[V];
    auto NewAttr = OldAttr | Attr;
    if (OldAttr == NewAttr)
      return false;
    OldAttr = NewAttr;
    return true;
  }

  AliasAttrs getAttrs(InstantiatedValue V) const {
    AliasAttrs Attr;
    auto Itr = AttrMap.find(V);
    if (Itr != AttrMap.end())
      Attr = Itr->second;
    return Attr;
  }

  iterator_range<const_iterator> mappings() const {
    return make_range<const_iterator>(AttrMap.begin(), AttrMap.end());
  }
};

struct WorkListItem {
  InstantiatedValue From;
  InstantiatedValue To;
  MatchState State;
};

struct CSListItem {
  InstantiatedValue From;
  InstantiatedValue To;
  MatchState State;
  CallSite CS;
};

} // end anonymous namespace

namespace llvm {

// Specialize DenseMapInfo for OffsetValue.
template <> struct DenseMapInfo<OffsetValue> {
  static OffsetValue getEmptyKey() {
    return OffsetValue{DenseMapInfo<const Value *>::getEmptyKey(),
                       DenseMapInfo<int64_t>::getEmptyKey()};
  }

  static OffsetValue getTombstoneKey() {
    return OffsetValue{DenseMapInfo<const Value *>::getTombstoneKey(),
                       DenseMapInfo<int64_t>::getEmptyKey()};
  }

  static unsigned getHashValue(const OffsetValue &OVal) {
    return DenseMapInfo<std::pair<const Value *, int64_t>>::getHashValue(
        std::make_pair(OVal.Val, OVal.Offset));
  }

  static bool isEqual(const OffsetValue &LHS, const OffsetValue &RHS) {
    return LHS == RHS;
  }
};

// Specialize DenseMapInfo for OffsetInstantiatedValue.
template <> struct DenseMapInfo<OffsetInstantiatedValue> {
  static OffsetInstantiatedValue getEmptyKey() {
    return OffsetInstantiatedValue{
        DenseMapInfo<InstantiatedValue>::getEmptyKey(),
        DenseMapInfo<int64_t>::getEmptyKey()};
  }

  static OffsetInstantiatedValue getTombstoneKey() {
    return OffsetInstantiatedValue{
        DenseMapInfo<InstantiatedValue>::getTombstoneKey(),
        DenseMapInfo<int64_t>::getEmptyKey()};
  }

  static unsigned getHashValue(const OffsetInstantiatedValue &OVal) {
    return DenseMapInfo<std::pair<InstantiatedValue, int64_t>>::getHashValue(
        std::make_pair(OVal.IVal, OVal.Offset));
  }

  static bool isEqual(const OffsetInstantiatedValue &LHS,
                      const OffsetInstantiatedValue &RHS) {
    return LHS == RHS;
  }
};


} // end namespace llvm

static void propagate(InstantiatedValue From, InstantiatedValue To,
                      MatchState State, ReachabilitySet &ReachSet,
                      std::vector<WorkListItem> &WorkList) {
  if (ReachSet.insert(From, To, State)) {
    if(isa<ConstantPointerNull>(To.Val))
      return;
    WorkList.push_back(WorkListItem{From, To, State});
  }

}

static void callSitePropagate(CSListItem Item, ReachabilitySet &ReachSet,
                      std::vector<CSListItem> &CSList) {
  if (ReachSet.insert(Item.From, Item.To, Item.State)) {
    if(isa<ConstantPointerNull>(Item.To.Val))
      return;
    CSList.push_back(Item);
  }

}
static void callSiteCleanup(const CSListItem& Item, ReachabilitySet &ReachSet, const CFLGraph &Graph, std::vector<WorkListItem> &WorkList) {
  auto From = Item.From;
  auto To = Item.To;
  ValueReachMap Map = ReachSet.getReachMap();
  //auto FuncName = Item.CS.getCalledFunction()->getName();
  //if (FuncName == "obj_descr_create")
  //  errs() << "clean up callsite " << *Item.CS.getInstruction() << " from " << From << " to " << To << " state " << Item.State << "\n";
  for (auto &AliasMapping: Map.reachableValueAliases(To)) {
    auto NewStates = composeStateSets(toStateSet(Item.State), AliasMapping.second);
    //if (FuncName == "obj_descr_create")
    //  errs() << "new alias " << AliasMapping.first << "\n";
    if (!ReachSet.insertStates(From, AliasMapping.first, NewStates))
      continue;
    if (auto *ValueInfo = Graph.getValueInfo(AliasMapping.first.Val)) {
      for (auto &Edge: ValueInfo->RetEdges)
        if (Item.CS == Edge.CS) {
    	  for (std::size_t i = 0; i < NewStates.size(); ++i)
    	    if (NewStates[i]) propagate(From, InstantiatedValue{Edge.Other, To.DerefLevel}, (MatchState)i, ReachSet, WorkList);
        }
      for (auto &Edge: ValueInfo->ReverseArgEdges)
        if (Item.CS == Edge.CS) {
    	  for (std::size_t i = 0; i < NewStates.size(); ++i)
    	    if (NewStates[i]) propagate(From, InstantiatedValue{Edge.Other, To.DerefLevel}, (MatchState)i, ReachSet, WorkList);
        }
    }
  }
}

static Optional<InstantiatedValue> getNodeBelow(const CFLGraph &Graph,
                                                InstantiatedValue V) {
  auto NodeBelow = InstantiatedValue{V.Val, V.DerefLevel + 1};
  if (Graph.getNode(NodeBelow))
    return NodeBelow;
  return None;
}

static Optional<InstantiatedValue> getNodeAbove(const CFLGraph &Graph,
                                                InstantiatedValue V) {
  if (V.DerefLevel == 0)
    return None;
  auto NodeAbove = InstantiatedValue{V.Val, V.DerefLevel - 1};
  if (Graph.getNode(NodeAbove))
    return NodeAbove;
  return None;
}

static void processWorkListItem(const WorkListItem &Item, const CFLGraph &Graph,
                                ReachabilitySet &ReachSet, AliasMemSet &MemSet,
                                std::vector<WorkListItem> &WorkList,
                                std::vector<CSListItem> &CSList) {

  auto FromNode = Item.From;
  auto ToNode = Item.To; 

  // FIXME: Here is a neat trick we can do: since both ReachSet and MemSet holds
  // relations that are symmetric, we could actually cut the storage by half by
  // sorting FromNode and ToNode before insertion happens.
  // with returnEdges ReachSet and MemSet are no longer symmetric

  // The newly added value alias pair may potentially generate more memory
  // alias pairs. Check for them here. 
    
  auto FromNodeBelow = getNodeBelow(Graph, FromNode);
  auto ToNodeBelow = getNodeBelow(Graph, ToNode);
   
  if (FromNodeBelow && ToNodeBelow && MemSet.insert(*FromNodeBelow, *ToNodeBelow)) {
    //propagate(*FromNodeBelow, *ToNodeBelow, MatchState::FlowFromMemAliasNoReadWrite,  ReachSet, WorkList, IsCallee);
    ValueReachMap Map = ReachSet.getRevReachMap();
    for (const auto &Mapping : Map.reachableValueAliases(*FromNodeBelow)) {
           auto Src = Mapping.first;
           if (Mapping.second.test(static_cast<size_t>(MatchState::FlowFromReadOnly)))
             propagate(Src, *ToNodeBelow, MatchState::FlowFromMemAliasReadOnly, ReachSet, WorkList);
           if (Mapping.second.test(static_cast<size_t>(MatchState::FlowToWriteOnly)))
             propagate(Src, *ToNodeBelow, MatchState::FlowToMemAliasWriteOnly, ReachSet, WorkList);
           if (Mapping.second.test(static_cast<size_t>(MatchState::FlowToReadWrite)))
             propagate(Src, *ToNodeBelow, MatchState::FlowToMemAliasReadWrite, ReachSet, WorkList);       
    }
  }

  // This is the core of the state machine walking algorithm. We expand ReachSet
  // based on which state we are at (which in turn dictates what edges we
  // should examine)
  // From a high-level point of view, the state machine here guarantees two
  // properties:
  // - If *X and *Y are memory aliases, then X and Y are value aliases
  // - If Y is an alias of X, then reverse assignment edges (if there is any)
  // should precede any assignment edges on the path from X to Y.

  auto ValueInfo = Graph.getValueInfo(ToNode.Val);
  assert(ValueInfo);
 
  auto startExplore = [&] (InstantiatedValue Node) {
    auto NodeInfo = Graph.getNode(Node);
    assert(NodeInfo);
    for (const auto &Edge : NodeInfo->Edges)
      propagate(Node, Edge.Other, MatchState::FlowToWriteOnly, ReachSet, WorkList);
    for (const auto &Edge : NodeInfo->ReverseEdges)
      propagate(Node, Edge.Other, MatchState::FlowFromReadOnly, ReachSet, WorkList);
  };

  for (const auto &Edge : ValueInfo->ArgEdges) {
	auto Other = InstantiatedValue{Edge.Other, ToNode.DerefLevel};
        callSitePropagate(CSListItem{FromNode, Other, Item.State, Edge.CS}, ReachSet, CSList);
        startExplore(Other);
  }
 
  auto NodeInfo = Graph.getNode(ToNode);
  if (NodeInfo) {
    auto NextAssignState = [&](MatchState State) {
      for (const auto &AssignEdge : NodeInfo->Edges)
        propagate(FromNode, AssignEdge.Other, State, ReachSet, WorkList);
    };
    auto NextRevAssignState = [&](MatchState State) {
      for (const auto &RevAssignEdge : NodeInfo->ReverseEdges)
        propagate(FromNode, RevAssignEdge.Other, State, ReachSet, WorkList);
    };
    auto NextMemState = [&](MatchState State) {
      if (const auto AliasSet = MemSet.getMemoryAliases(ToNode))
        for (const auto &MemAlias : *AliasSet)
  	  propagate(FromNode, MemAlias, State, ReachSet, WorkList);
    };
    
    if(auto AfterRead = applyRead(Item.State))
      NextRevAssignState(*AfterRead);
    
    NextAssignState(applyWrite(Item.State));
    
    if(auto AfterMem = applyMemAlias(Item.State))
      NextMemState(*AfterMem);
  }

  auto ToNodeAbove = getNodeAbove(Graph, ToNode);
  if (hasNonMemAliasState(toStateSet(Item.State)) && ToNodeAbove) 
  {
    startExplore(*ToNodeAbove);
  }
}

static void exploreFromNode(InstantiatedValue Node, const CFLGraph &Graph,
                            ReachabilitySet &ReachSet, AliasMemSet &MemSet) {
  std::vector<WorkListItem> WorkList, NextList;
  std::vector<CSListItem> CSList;
  auto NodeInfo = Graph.getNode(Node);

  assert(NodeInfo);

  for (const auto &Edge : NodeInfo->Edges)
    propagate(Node, Edge.Other, MatchState::FlowToWriteOnly, ReachSet,
      WorkList);

  while (!WorkList.empty()) {
    while (!WorkList.empty()) {
      for (auto Itr = WorkList.rbegin(); Itr != WorkList.rend(); Itr++) {
        processWorkListItem(*Itr, Graph, ReachSet, MemSet, NextList, CSList);
      }

      NextList.swap(WorkList);
      NextList.clear();
    }

    for (auto Itr = CSList.begin(); Itr != CSList.end(); Itr++) {
      callSiteCleanup(*Itr, ReachSet, Graph, WorkList);
    }
  }
}

static void processWorkList(ReachabilitySet &ReachSet,
                               AliasMemSet &MemSet,
                               const CFLGraph &Graph,
                               const TaintedSet &TaintedVals) {
  for (const auto &Mapping : Graph.value_mappings()) {
    auto Val = Mapping.first;
    auto &ValueInfo = Mapping.second;
    assert(ValueInfo.getNumLevels() > 0);

    //value is a taint source at some level
    unsigned LowerBound = 0;
    for (unsigned I = 0, E = ValueInfo.getNumLevels(); I < E; I++) {
      if (TaintedVals.count(InstantiatedValue{Val, I}))
        LowerBound = I + 1;
    }
    for (unsigned I = 0; I < LowerBound; I++) {
      auto Src = InstantiatedValue{Val, I};
      exploreFromNode(Src, Graph, ReachSet, MemSet);
    } 
  }
}

bool buildTaintedValMap(DenseMap<const Function *, DenseSet<Value *>> &TaintedValMap, TaintedSet &TaintSources, const ValueReachMap &ReachMap, const GEPMapType &GEPMap) {
  bool Changed = false;
  TaintedSet Copy = TaintSources;
  for (const auto &Mapping: Copy) {
    auto IVal = Mapping.first;
    auto Fn = parentFunctionOfValue(IVal.Val);
    if(isa<ConstantPointerNull>(IVal.Val))
      continue;
    if (IVal.DerefLevel == 0 && Fn)
      TaintedValMap[Fn].insert(IVal.Val);

    for (const auto &AliasMapping: ReachMap.reachableValueAliases(IVal)) {
      auto Alias = AliasMapping.first;
      if(isa<ConstantPointerNull>(Alias.Val))
        continue;
      const auto AliasFn = parentFunctionOfValue(Alias.Val);
      if (!AliasFn)
  	    continue;
      //if (AliasFn->getName() == "obj_descr_create")
      //  errs() << "Alias " << *Alias.Val << " of source " << *IVal.Val << "\n";
      if (Alias.DerefLevel == 0)
        TaintedValMap[AliasFn].insert(Alias.Val);
  
      auto AddField = [&] (StructType *StructTy, uint64_t Offset) {
  	    auto StructItr = GEPMap.find(StructTy);
        if (StructItr == GEPMap.end()) 
          return;
  
  	    auto OffsetItr = StructItr->second.find(Offset);
  	    if (OffsetItr ==StructItr->second.end()) 
  	      return;
  
  	    for (auto *GEPOpAlias: OffsetItr->second)
  	      Changed |= TaintSources.addStates(InstantiatedValue{GEPOpAlias, Alias.DerefLevel}, AliasMapping.second).any();
      };
  
      auto AddAllFields = [&] (StructType *StructTy) {
  	    auto StructItr = GEPMap.find(StructTy);
  	    if (StructItr == GEPMap.end()) 
          return;
  
  	    for (auto &Mapping: StructItr->second)
  	      for (auto &GEPOpAlias: Mapping.second)
  	        Changed |= TaintSources.addStates(InstantiatedValue{GEPOpAlias, Alias.DerefLevel}, AliasMapping.second).any();
      };
  
      auto DL = AliasFn->getParent()->getDataLayout();
      if (auto *GEPOp = dyn_cast<GEPOperator>(Alias.Val)) {
        if (auto *StructTy = dyn_cast<StructType>(GEPOp->getSourceElementType())) {
  	    uint64_t Offset = getGEPOffset(*GEPOp, DL);
  	    if (Offset == UnknownOffset)
  	      AddAllFields(StructTy);
  	    else
  	      AddField(StructTy, Offset);
  	    }
      }
     
      if (auto *StructTy = dyn_cast<StructType>(cast<PointerType>(Alias.Val->getType())->getElementType()))
  	    AddAllFields(StructTy);
    }
  }
  return Changed;
}

static void processAnnotation(Module &M) {
  for (auto Pair: PMAllocatorAnnos) {
    if (auto* Fn = M.getFunction(Pair.FnName))
      Fn->addFnAttr(PMAllocAnno, Pair.Anno);
  }

  GlobalVariable *GlobalAnnos = M.getNamedGlobal("llvm.global.annotations");
  if (!GlobalAnnos)
    return;

  ConstantArray *A = cast<ConstantArray>(GlobalAnnos->getOperand(0));
  for (unsigned I=0; I < A->getNumOperands(); I++) {
    ConstantStruct *E = cast<ConstantStruct>(A->getOperand(I));
    if (Function *Fn = dyn_cast<Function>(E->getOperand(0)->getOperand(0))) {
      StringRef Anno = cast<ConstantDataArray>(cast<GlobalVariable>(E->getOperand(1)->getOperand(0))->getOperand(0))->getAsCString();
      std::pair<StringRef, StringRef> Split = Anno.split(":");
      if (Split.first == PMAllocAnno)
        Fn->addFnAttr(Split.first, Split.second);
    }
  }
}

void
CFLAndersTaintResult::buildInfoFrom(const Module &M) {  
  CFLGraphBuilder<CFLAndersTaintResult> GraphBuilder(
      *this, TLI,
      // Cast away the constness here due to GraphBuilder's API requirement
      const_cast<Module &>(M)
    );
  auto &Graph = GraphBuilder.getCFLGraph();
  auto &GEPMap = GraphBuilder.getGEPMap();
  TaintedSet TaintSources = Graph.getTainted();
 
  ReachabilitySet ReachSet;
  AliasMemSet MemSet;
  bool Changed = true;
  while (Changed) {
    processWorkList(ReachSet, MemSet, Graph, TaintSources); 
    auto ReachMap = ReachSet.getReachMap();
    Changed = buildTaintedValMap(TaintedValMap, TaintSources, ReachMap, GEPMap);
  }

  //for (auto &Pair: TaintedValMap) {
  //  if (Pair.first->getName() == "obj_descr_create") {
  //    errs() << "tainted in " << Pair.first->getName() << "------------------\n";
  //    for (auto Val: Pair.second)
  //      errs() << *Val << "\n";
  //  }
  //}
}

Optional<DenseSet<Value *>> CFLAndersTaintResult::taintedVals(const Function &Fn) {
    auto Itr = TaintedValMap.find(&Fn);
    if(Itr == TaintedValMap.end())
      return None;
    return Itr->second;
}

DenseMap<const Function *, DenseSet<Value *>> CFLAndersTaintResult::taintedValsInReachableFuncs(const Function &Fn) {
  return TaintedValMap;
}

AnalysisKey CFLAndersAA::Key;

CFLAndersTaintResult CFLAndersAA::run(Function &F, FunctionAnalysisManager &AM) {
  return CFLAndersTaintResult(AM.getResult<TargetLibraryAnalysis>(F));
}

char CFLAndersTaintWrapperPass::ID = 0;
static RegisterPass<CFLAndersTaintWrapperPass> X("cfl-anders-taint", "Inclusion-Based CFL Taint Analysis", false, true);


//INITIALIZE_PASS(CFLAndersTaintWrapperPass, "cfl-anders-taint",
//                "Inclusion-Based CFL Taint Analysis", false, true)


bool CFLAndersTaintWrapperPass::runOnModule(Module &M) {
  auto &TLIWP = getAnalysis<TargetLibraryInfoWrapperPass>();
  Result.reset(new CFLAndersTaintResult(TLIWP.getTLI()));
  processAnnotation(M);
  Result->buildInfoFrom(M);
  return true;
}

CFLAndersTaintWrapperPass::CFLAndersTaintWrapperPass() : ModulePass(ID) {
  //initializeCFLAndersTaintWrapperPassPass(*PassRegistry::getPassRegistry());
}

//void CFLAndersTaintWrapperPass::initializePass() {
//  auto &TLIWP = getAnalysis<TargetLibraryInfoWrapperPass>();
//  Result.reset(new CFLAndersTaintResult(TLIWP.getTLI()));
//}

void CFLAndersTaintWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<TargetLibraryInfoWrapperPass>();
}
