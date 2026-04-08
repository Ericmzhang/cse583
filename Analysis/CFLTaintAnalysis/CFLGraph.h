//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
/// \file
/// This file defines CFLGraph, an auxiliary data structure used by CFL-based
/// alias analysis.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_ANALYSIS_TAINT_CFLGRAPH_H
#define LLVM_LIB_ANALYSIS_TAINT_CFLGRAPH_H

#include "AliasAnalysisSummary.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include <vector>

namespace llvm {
namespace cflta {

/// The Program Expression Graph (PEG) of CFL analysis
/// CFLGraph is auxiliary data structure used by CFL-based alias analysis to
/// describe flow-insensitive pointer-related behaviors. Given an LLVM function,
/// the main purpose of this graph is to abstract away unrelated facts and
/// translate the rest into a form that can be easily digested by CFL analyses.
/// Each Node in the graph is an InstantiatedValue, and each edge represent a
/// pointer assignment between InstantiatedValue. Pointer
/// references/dereferences are not explicitly stored in the graph: we
/// implicitly assume that for each //node (X, I) it has a dereference edge to (X,
/// I+1) and a reference edge to (X, I-1).

class CFLGraph {

public:
  CFLGraph();

  using Node = InstantiatedValue;

  struct Edge {
    Node Other;
    int64_t Offset;
  };

   //function arguments can propagate aliases both in and out of functions, return values can only propagate out of functions. 
  struct CallEdge {
    Value *Other;
    CallSite CS; 
  };

  using EdgeList = std::vector<Edge>;
  using CallEdgeList = std::vector<CallEdge>;

  struct NodeInfo {
    EdgeList Edges, ReverseEdges;
    AliasAttrs Attr;
  };

  class ValueInfo {
    std::vector<NodeInfo> Levels;

  public:
    
    CallEdgeList ArgEdges, ReverseArgEdges, RetEdges;

	bool addNodeToLevel(unsigned Level);

    NodeInfo &getNodeInfoAtLevel(unsigned Level);

    const NodeInfo &getNodeInfoAtLevel(unsigned Level) const;

    unsigned getNumLevels() const;

  };

private:
  using ValueMap = DenseMap<Value *, ValueInfo>;

  ValueMap ValueImpls;
    
  TaintedSet Tainted;

  ValueInfo *getValueInfo(Value *V);

  NodeInfo *getNode(Node N);
 
  void addTaintByAttributes(Node N, AliasAttrs Attr);

public:
  using const_value_iterator = ValueMap::const_iterator;

  unsigned getCurMaxLevel(const Value* Val) const; 

  bool addNode(Node N, AliasAttrs Attr = AliasAttrs(), StateSet TaintStates = StateSet());

  void addAttr(Node N, AliasAttrs Attr);

  void addEdge(Node From, Node To, int64_t Offset = 0);
  
  void addArgEdge(Value *From, Value *To, CallSite CS);
  
  void addRetEdge(Value *From, Value *To, CallSite CS);

  const ValueInfo *getValueInfo(Value *V) const; 

  const NodeInfo *getNode(Node N) const;  

  AliasAttrs attrFor(Node N) const;
  
  iterator_range<const_value_iterator> value_mappings() const;

  const TaintedSet &getTainted() const;
  
  void propagateLevels(); 
};

} // end namespace cflta
} // end namespace llvm
#endif // LLVM_LIB_ANALYSIS_CFLGRAPH_H
