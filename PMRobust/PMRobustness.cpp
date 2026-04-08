//===-- PMRobustness.cpp - xxx -------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file is a modified version of ThreadSanitizer.cpp, a part of a race detector.
//
// The tool is under development, for the details about previous versions see
// http://code.google.com/p/data-race-test
//
// The instrumentation phase is quite simple:
//	 - Insert calls to run-time library before every memory access.
//		- Optimizations may apply to avoid instrumenting some of the accesses.
//	 - Insert calls at function entry/exit.
// The rest is handled by the run-time library.
//===----------------------------------------------------------------------===//
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/None.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallSet.h"
#include "../Analysis/CFLTaintAnalysis/CFLAndersTaintAnalysis.h"

#include "FlushUtils.h"
#include "FunctionSummary.h"
#include "PMRobustness.h"
#include "AnnotatedFuncs.h"

#include <cxxabi.h>


//#define PMROBUST_DEBUG
//#define DUMP_CACHED_RESULT
//#define DUMP_INST_STATE
//#define DUMP_BLOCK_STATE
//#define DUMP_BLOCK_DIFF_STATE

#define INTERPROCEDURAL

const std::string DBG_FUNCS[] = {""}; 
const std::string DBG_BLOCKS[] = {""}; 
const std::string IGNORE = "ignore";
const std::string FLIT_SHARED_STORE = "flit_shared_store";
const std::string FLIT_LOAD = "flit_load";
const std::string RELEASE_OBJ_FENCE = "release_obj_fence";
const std::string MULTI_OBJ_FENCE = "multi_obj_fence";
const std::string MULTI_FIELD_FENCE = "multi_field_fence";
const std::string PTR_ARITH_FENCE = "ptr_arith_fence";
const std::string FUNC_END_FENCE = "func_end_fence";
const std::string BLOCK_END_FENCE = "block_end_fence";
const std::string SEQ_CST_FENCE = "seq_cst_fence";

inline bool shouldDebug(Function *F) {
	return DBG_FUNCS[0]=="" || std::find(std::begin(DBG_FUNCS), std::end(DBG_FUNCS), F->getName().str()) != std::end(DBG_FUNCS);
}

inline bool shouldDebug(BasicBlock *B) {
	return DBG_BLOCKS[0]=="" || std::find(std::begin(DBG_BLOCKS), std::end(DBG_BLOCKS), B->getName().str()) != std::end(DBG_BLOCKS);
}

enum FlushInsMode {
  NO_FLUSH, OPTIMIZED, NAIVE
};

cl::opt<FlushInsMode> FlushInsertMode("insert-flush", cl::desc("Choose mode of flush insertion:"),
  cl::values(
	clEnumValN(NO_FLUSH, "none", "no flush insertion"),
	clEnumValN(OPTIMIZED, "opt", "optimized flush insertion based on flush state tracking"),
	clEnumValN(NAIVE, "naive", "naive flush insertion")
  ), 
  cl::init(NO_FLUSH));

cl::opt<bool> Flit("flit", cl::desc("Use flit transformation"));

cl::opt<bool> BlockEndFence("block-end-fence", cl::desc("Insert fence when block a block that needs a fence merges with other blocks that don't"));

int getAtomicOrderIndex(AtomicOrdering order) {
	switch (order) {
		case AtomicOrdering::Monotonic:
			return (int)AtomicOrderingCABI::relaxed;
		//case AtomicOrdering::Consume:		// not specified yet
		//	return AtomicOrderingCABI::consume;
		case AtomicOrdering::Acquire:
			return (int)AtomicOrderingCABI::acquire;
		case AtomicOrdering::Release:
			return (int)AtomicOrderingCABI::release;
		case AtomicOrdering::AcquireRelease:
			return (int)AtomicOrderingCABI::acq_rel;
		case AtomicOrdering::SequentiallyConsistent:
			return (int)AtomicOrderingCABI::seq_cst;
		default:
			// unordered or Not Atomic
			return -1;
	}
}

static inline bool isUnsafeState(ob_state_t *state) {
	return (state->isDirty() || state->isClwb()) && state->isEscaped();
}

static inline std::string demangle(const StringRef ref) {
	char* demangled;
	if ((demangled = abi::__cxa_demangle(ref.begin(), 0, 0, NULL))) {
		auto s = std::string(demangled);
		free(demangled);
		return s;
	}
	return ref.str();
}

namespace {
	struct PMRobustness : public ModulePass {
		PMRobustness() : ModulePass(ID) {}
		StringRef getPassName() const override;
		bool doInitialization(Module &M) override;
		bool runOnModule(Module &M) override;
		void getAnalysisUsage(AnalysisUsage &AU) const override;
		void analyzeFunction(Function &F, CallingContext *Context);

		static char ID;
		CFLAndersTaintResult *CFL;

	private:
		void copyState(state_t * src, state_t * dst);
		void copyArrayState(addr_set_t &src, addr_set_t &dst);
		bool copyStateCheckDiff(state_t * src, state_t * dst);

		void copyMergedState(state_map_t *AbsState, SmallSetVector<BasicBlock *, 8> &src_list, state_t * dst);
		void copyMergedArrayState(DenseMap<BasicBlock *, addr_set_t> &ArraySets,
			SmallSetVector<BasicBlock *, 8> &src_list, addr_set_t &dst);

		void processInstruction(state_t * map, Instruction * I);
		bool processAtomic(state_t * map, Instruction * I, bool &report_release_error);
		bool processMemIntrinsic(state_t * map, Instruction * I);
		bool processLoad(state_t * map, Instruction * I);
		bool processStore(state_t * map, Instruction * I);
		bool processPHI(state_t * map, Instruction * I);
		bool processSelect(state_t * map, Instruction * I);
		bool processFence(state_t * map, Instruction * I);
		void processMutexUnlock(state_t * map, Instruction * I);

		void processFlush(state_t *map, Instruction *I, NVMOP op);
		void processInFunctionAnnotation(Instruction *I);
		bool processAnnotatedFunction(state_t *map, Instruction *I, bool &check_error);
		void processFlushWrapperFunction(state_t *map, Instruction * I);
		void processFlushParameterFunction(state_t *map, Instruction * I);
		void processReturnAnnotation(state_t *map, Instruction *I);
		void processPMMemcpy(state_t *map, Instruction *I);
		void processCalls(state_t *map, Instruction *I, bool &non_dirty_escaped_before, bool &report_release_error);
		void getAnnotatedParamaters(std::string attr, std::vector<StringRef> &annotations, Function *callee);

		bool skipAnnotatedInstruction(Instruction *I);
		bool skipFunction(Function &F);
		// TODO: Address check to be implemented
		bool isPMAddr(const Function *F, const Value * Addr, const DataLayout &DL);
		bool mayInHeap(const Value * Addr);
		ob_state_t * getObjectState(state_t *map, const Value *Addr, bool &updated);
		ob_state_t * getObjectState(state_t *map, const Value *Addr);
		void removeNVMOp(Instruction *I);
		void preprocessDirtyObj(Instruction *I, const DataLayout &DL);
		void preprocessInsts(Module &M);
		void fenceIfDifferentClwbStates(SmallSetVector<BasicBlock *, 8> &pred_list, state_map_t *AbsState);
		CallInst *fenceAndChangeState(Instruction *I, state_t *state);

		void checkEndError(state_map_t *AbsState, Function &F);
		bool checkUnsafeObj(state_t *map, Instruction *I, bool non_dirty_escaped_before);
		void checkMultiObjError(state_t *map, Instruction *I, bool non_dirty_escaped_before);
		void checkReleaseError(state_t *map, Instruction *I);
		void reportMultipleEscDirtyFieldsError(state_t *map, Instruction *I);

		void decomposeAddress(DecomposedGEP &DecompGEP, Value *Addr, const DataLayout &DL);
		unsigned getMemoryAccessSize(Value *Addr, const DataLayout &DL);
		unsigned getFieldSize(Value *Addr, const DataLayout &DL);
		NVMOP whichNVMoperation(Instruction *I);
		NVMOP whichNVMoperation(StringRef flushtype);
		NVMOP analyzeFlushType(Function &F);
		bool isInFunctionAnnotation(Instruction *I);
		bool isFunctionAnnotated(Instruction *I);
		bool isFunctionAnnotated(Function &F);
		bool isFlushWrapperFunction(Instruction *I);
		bool isMutexLock(Instruction *I);
		bool isMutexUnlock(Instruction *I);

		addr_set_t * getUnflushedAddrSet(Function *F, BasicBlock *B);
		bool checkUnflushedAddress(Function *F, addr_set_t * AddrSet, Value * Addr, NVMOP op);
		bool checkPointerArithmetics(Value *Addr, const DataLayout &DL);
		bool compareDecomposedGEP(DecomposedGEP &GEP1, DecomposedGEP &GEP2);

		CallingContext * computeContext(state_t *map, Instruction *I);
		void lookupFunctionResult(state_t *map, CallBase *CB, CallingContext *Context,
				bool &non_dirty_escaped_before, bool &report_release_error);
		void computeInitialState(state_t *map, Function &F, CallingContext *Context);
		bool computeFinalState(state_map_t *AbsState, Function &F, CallingContext *Context);
		FunctionSummary * getOrCreateFunctionSummary(Function *F);

		void makeParametersTOP(state_t *map, CallBase *CB);
		void modifyReturnState(state_t *map, CallBase *CB, OutputState *out_state);

		alias_set_t * getFunctionAliasSet(Function *F);
		value_set_t * getValueAliasSet(Function *F, Value *V);
		void computeAliasSet(PHINode *PHI);

		const Value * GetLinearExpression(
			const Value *V, APInt &Scale, APInt &Offset, unsigned &ZExtBits,
			unsigned &SExtBits, const DataLayout &DL, unsigned Depth,
			AssumptionCache *AC, DominatorTree *DT, bool &NSW, bool &NUW
		);

		bool DecomposeGEPExpression(const Value *V, DecomposedGEP &Decomposed,
			const DataLayout &DL, AssumptionCache *AC, DominatorTree *DT
		);

		void printMap(state_t * map);
		void test();

		// object states at the end of each instruction for each function
		DenseMap<const Function *, state_map_t> AbstractStates;
		// object states at the end of each basic block for each function
		DenseMap<const Function *, b_state_map_t> BlockEndAbstractStates;

		/* typedef DenseMap<const Value *, ArrayInfo> addr_set_t; */
		DenseMap<const Function *, DenseMap<BasicBlock *, addr_set_t>> UnflushedArrays;
		DenseMap<const Function *, FunctionSummary> FunctionSummaries;
		DenseMap<const Function *, SmallPtrSet<Instruction *, 8>> FunctionRetInstMap;

		// atomic RMW (CAS), seq_cst load, concurrency fence, mutex lock
		DenseMap<const Function *, DenseMap<const BasicBlock *, bool>> FenceAnalysisMap;

		CallingContext *CurrentContext;

		// Arguments of the function being analyzed
		DenseMap<const Value *, unsigned> FunctionArguments;

		// Map a Function to its call sites
		DenseMap<Function *, SetVector<std::pair<Function *, CallingContext *>> > FunctionCallerMap;

		DenseMap<const Function*, DenseSet<Value *>> PMAddrSets;

		std::list<std::pair<Function *, CallingContext *>> FunctionWorklist;

		// The set of items in FunctionWorklist; used to avoid insert duplicate items to FunctionWorklist
		DenseSet<std::pair<Function *, CallingContext *>> UniqueFunctionSet;

		DenseMap<const BasicBlock *, bool> visited_blocks;
		std::list<BasicBlock *> BlockWorklist;

		DenseMap<const Function *, DenseSet<const Value *>> FunctionEndErrorSets;
		DenseMap<const Function *, DenseSet<const Instruction *>> FunctionStmtErrorSets;
		DenseSet<const Instruction *> * StmtErrorSet;
		bool HasTwoUnsafeParams;
		bool InstructionMarksEscDirObj;	// Instruction: current instruction
		bool FunctionMarksEscDirObj;	// Function: this function

		// Call: this call instruction marks any object as dirty and escaped when no parameters are dirty and escaped;
		bool CallMarksEscDirObj;
		std::string MultiUnsafeFieldsPrevPos;

		unsigned MaxLookupSearchDepth = 100;
		std::vector<StringRef> AnnotationList;

		DenseMap<const Function *, alias_set_t *> FunctionAliasSet;
		LLVMContext *Ctx;
		Function *VarSizedFlush;
		Function *GetFlitCounter;
		IntegerType *FlitCounterType;
	};
}

StringRef PMRobustness::getPassName() const {
	return "PMRobustness";
}

static Function *checkPMRobustInterfaceFunction(Value *FuncOrBitcast) {
	if (isa<Function>(FuncOrBitcast))
		return cast<Function>(FuncOrBitcast);
	FuncOrBitcast->print(errs());
	errs() << '\n';
	std::string Err;
	raw_string_ostream Stream(Err);
	Stream << "PMRobust interface function redefined: " << *FuncOrBitcast;
	report_fatal_error(Err);
} 

/* annotations -> myflush:[addr|size|ignore] */
bool PMRobustness::doInitialization (Module &M) {
		Ctx = &M.getContext();
	PointerType *ptrType = Type::getInt8PtrTy(*Ctx);
	IntegerType *int64Type = Type::getInt64Ty(*Ctx);
	IntegerType *int32Type = Type::getInt32Ty(*Ctx);
	Type *voidType = Type::getVoidTy(*Ctx);

	VarSizedFlush = checkPMRobustInterfaceFunction(M.getOrInsertFunction("my_clflush", voidType, ptrType, int32Type));
	if (Flit) {
		FlitCounterType = int64Type;
		GetFlitCounter = checkPMRobustInterfaceFunction(M.getOrInsertFunction("get_flit_counter", FlitCounterType->getPointerTo(), ptrType));
	}

	AnnotationList = {
		"myflush", "flush_parameter", "preprocess_ignore", "ignore", "suppress", "return",
		"persist_memcpy"
	};

	GlobalVariable *global_annos = M.getNamedGlobal("llvm.global.annotations");
	if (global_annos) {
		ConstantArray *a = cast<ConstantArray>(global_annos->getOperand(0));
		for (unsigned i=0; i < a->getNumOperands(); i++) {
			ConstantStruct *e = cast<ConstantStruct>(a->getOperand(i));
			if (Function *fn = dyn_cast<Function>(e->getOperand(0)->getOperand(0))) {
				StringRef anno = cast<ConstantDataArray>(cast<GlobalVariable>(e->getOperand(1)->getOperand(0))->getOperand(0))->getAsCString();
				std::pair<StringRef, StringRef> Split = anno.split(":");
				fn->addFnAttr(Split.first, Split.second);
			}
		}
	}

	for (auto &pair: AnnotatedFuncs) {
		if (auto *fn = M.getFunction(pair.first)) {
			StringRef anno = pair.second;
			std::pair<StringRef, StringRef> Split = anno.split(":");
			fn->addFnAttr(Split.first, Split.second);
		}
	}

	return true;
}

void PMRobustness::removeNVMOp(Instruction *I) {
	if (I->isTerminator()) {
		auto II = cast<InvokeInst>(I); //only invoke instruction should be possible
		auto BI = BranchInst::Create(II->getNormalDest(), II);
	}
	I->eraseFromParent();
} 

void PMRobustness::preprocessDirtyObj(Instruction *I, const DataLayout &DL) {
	Value *Addr = nullptr;
	Value *Size = nullptr;
	IRBuilder<> builder(I->getNextNode());
	bool shouldFence = FlushInsertMode == NAIVE;
	
	if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
		auto atomic_order_index = getAtomicOrderIndex(SI->getOrdering());
		//allow flush to be inserted before the seq_cst fence
		if (atomic_order_index == (int)AtomicOrderingCABI::seq_cst) {
			SI->setOrdering(AtomicOrdering::Release);
			if (!Flit)
				shouldFence = true;
		}
		Addr = SI->getPointerOperand();
	} else if (AtomicRMWInst *RMWI = dyn_cast<AtomicRMWInst>(I)) {
		Addr = RMWI->getPointerOperand();
	} else if (AtomicCmpXchgInst *CASI = dyn_cast<AtomicCmpXchgInst>(I)) {
		Addr = CASI->getPointerOperand();
	} else if (I->isAtomic() && isa<LoadInst>(I)) {
		Addr = cast<LoadInst>(I)->getPointerOperand();
	} else if (auto MI = dyn_cast<MemIntrinsic>(I)) {
	    Addr = MI->getRawDest();
	    Size = MI->getLength();
	} else if (auto CB = dyn_cast<CallBase>(I)) {
	//PMMemcpy
		auto callee = CB->getCalledFunction();
		if (!callee || !callee->hasFnAttribute("persist_memcpy"))
			return;
		std::vector<StringRef> annotations;
		getAnnotatedParamaters("persist_memcpy", annotations, callee);
		unsigned i = std::find(annotations.begin(), annotations.end(), "addr") - annotations.begin();
		unsigned j = std::find(annotations.begin(), annotations.end(), "size") - annotations.begin();
		if (i > annotations.size() || j > annotations.size())
			return;

		Addr = CB->getArgOperand(i);
		Size = CB->getArgOperand(j);
	} else 
	return;
	
	if (!Addr->getType()->isPointerTy() || !isPMAddr(I->getFunction(), Addr, DL))
		return;

	DILocation *loc = I->getDebugLoc();
	MDNode *N = MDNode::get(*Ctx, None);
	if (I->isAtomic() && isa<LoadInst>(I) && Flit) {
		Value *AddrCast = builder.CreatePointerCast(Addr, GetFlitCounter->getFunctionType()->getParamType(0));
		CallInst *call = builder.CreateCall(GetFlitCounter, {AddrCast}, "flit_counter");
		call->setDebugLoc(loc);
		LoadInst *load = builder.CreateLoad(FlitCounterType, call);
		load->setOrdering(AtomicOrdering::SequentiallyConsistent);
		load->setAlignment(FlitCounterType->getBitWidth());
		Value *cond = builder.CreateICmpNE(load, ConstantInt::get(*Ctx, APInt(FlitCounterType->getBitWidth(), 0)), "flit_load_cond");
		Instruction *thenTerm = SplitBlockAndInsertIfThen(cond, &*builder.GetInsertPoint(), false); 
		builder.SetInsertPoint(thenTerm);
		I->setMetadata(FLIT_LOAD, N);
	} else if (I->isAtomic() && !isa<LoadInst>(I) && Flit) {
	    builder.SetInsertPoint(I);
	    Value *AddrCast = builder.CreatePointerCast(Addr, GetFlitCounter->getFunctionType()->getParamType(0));
		CallInst *call = builder.CreateCall(GetFlitCounter, {AddrCast}, "flit_counter");
	    call->setDebugLoc(loc);
	    ConstantInt *constOne = ConstantInt::get(*Ctx, APInt(FlitCounterType->getBitWidth(), 1));
	    builder.CreateAtomicRMW(AtomicRMWInst::Add, call, constOne, AtomicOrdering::SequentiallyConsistent);
	    builder.SetInsertPoint(I->getNextNode());
	    auto fsub = builder.CreateAtomicRMW(AtomicRMWInst::Sub, call, constOne, AtomicOrdering::SequentiallyConsistent);
	    builder.SetInsertPoint(fsub);
	    I->setMetadata(FLIT_SHARED_STORE, N);
	}

	if (Size && (!isa<ConstantInt>(Size) || cast<ConstantInt>(Size)->getZExtValue() >= MAX_RANGE_FLUSH)) {
		Value  *cast = builder.CreateIntCast(Size, VarSizedFlush->getFunctionType()->getParamType(1), false);
		CallInst *call = builder.CreateCall(VarSizedFlush, {Addr, cast});
		call->setDebugLoc(loc);
	} else if (Size && isa<ConstantInt>(Size)) {
	    unsigned size = cast<ConstantInt>(Size)->getZExtValue();
		insertFlushRange(builder, Addr, 0, size);
	} else { 
		unsigned size = getMemoryAccessSize(Addr, DL);
		insertFlushRange(builder, Addr, 0, size);
	}

	if (shouldFence) {
		MDNode *N = MDNode::get(*Ctx, None);
		auto fence = insertSFence(builder);
		fence->setMetadata(SEQ_CST_FENCE, N);
	}
}

void PMRobustness::preprocessInsts(Module &M) {
	const DataLayout &DL = M.getDataLayout();
	for (Function &F : M) {
        int i = 0;
	    if (F.hasFnAttribute("preprocess_ignore") || F.hasFnAttribute("ignore"))
		    continue;
		for (auto FItr = F.begin(); FItr != F.end();) {
		    BasicBlock *BB = &*FItr;
		    FItr++;
		    for (auto BItr = BB->begin(); BItr != BB->end();) {
		    	Instruction *I = &*BItr;
		    	BItr++;
		        //instructions and blocks may be inserted before BItr
		        if (skipAnnotatedInstruction(I)) {
		        	continue;
		        } else if (isInFunctionAnnotation(I)) {
		        	processInFunctionAnnotation(I);
		        } else if (isFlushWrapperFunction(I) || whichNVMoperation(I) != NVM_UNKNOWN) {
		        	removeNVMOp(I);	
		        } else if (!I->isTerminator()) {
		        	preprocessDirtyObj(I, DL);
                    if (BItr->getParent() != BB)
		        	BB = BItr->getParent();
		        }
		    }
        }
	}
}

void PMRobustness::fenceIfDifferentClwbStates(SmallSetVector<BasicBlock *, 8> &pred_list, state_map_t *AbsState) {
	auto hasClwbState = [&](BasicBlock *block){
	if (!visited_blocks[block])
		return false;

		auto itr = AbsState->find(block->getTerminator());
		if (itr == AbsState->end())
			return false;

		for (auto &pair: itr->second) {
			if (pair.second->isClwb()) {
				return true;
            }
		}
		return false;
	};

	SmallSetVector<BasicBlock *, 8> clwbBlocks;
	for (auto block: pred_list)
		if (hasClwbState(block))  {
			clwbBlocks.insert(block);
		}

	if (clwbBlocks.size() < pred_list.size()) {
		SmallSetVector<BasicBlock *, 8> succ_list;
			for (auto block: clwbBlocks) {
			auto terminator = block->getTerminator();
			auto state = &(*AbsState)[terminator];
			auto fence = fenceAndChangeState(terminator, state);
			MDNode *N = MDNode::get(*Ctx, None);
			fence->setMetadata(BLOCK_END_FENCE, N);
			for (BasicBlock *succ: successors(block)) {
				succ_list.insert(succ);
			}
			}

		for (BasicBlock *succ : succ_list) {
			BlockWorklist.push_back(succ);
		}
	}
}

CallInst *PMRobustness::fenceAndChangeState(Instruction *I, state_t *state) {
	//errs() << "insert fence before " << *I << "\n";
	IRBuilder<> builder(I);
	auto fence = insertSFence(builder);
	processFence(state, fence);
	return fence;
}

bool PMRobustness::runOnModule(Module &M) {
	const DataLayout &DL = M.getDataLayout();
	CFL = &getAnalysis<CFLAndersTaintWrapperPass>().getResult();
	
	if (FlushInsertMode == NAIVE) {
		preprocessInsts(M);
		return true;
	}
	if (FlushInsertMode == OPTIMIZED) {
	}

	for (Function &F : M) {
#ifdef INTERPROCEDURAL
		if (F.getName() == "main") {
			// Function has parameters
			CallingContext *Context = new CallingContext();
			for (unsigned i = 0; i < F.arg_size(); i++)
				Context->addAbsInput(ParamStateType::NON_PMEM);

			FunctionWorklist.emplace_back(&F, Context);
			UniqueFunctionSet.insert(std::make_pair(&F, Context));
		} else if (!F.isDeclaration()) {
			// Assume parameters have states TOP or do not push them to worklist?
			CallingContext *Context = new CallingContext();
			for (Function::arg_iterator it = F.arg_begin(); it != F.arg_end(); it++) {
				Argument *Arg = &*it;
				if (Arg->getType()->isPointerTy())
					Context->addAbsInput(ParamStateType::TOP);
				else
					Context->addAbsInput(ParamStateType::NON_PMEM);
			}

			FunctionWorklist.emplace_back(&F, Context);
			UniqueFunctionSet.insert(std::make_pair(&F, Context));
		} else {
			// F.isDeclaration
			//errs() << F.getName() << " isDeclaration ignored in Module " << M.getName() << "\n";

 #ifdef PMROBUST_DEBUG
			errs() << "{" << F.empty() << "," << !F.isMaterializable() << "}\n";
			errs() << F.getName() << " isDeclaration ignored\n";
 #endif
		}
#else
		if (!F.isDeclaration())
			FunctionWorklist.emplace_back(&F, new CallingContext());
#endif
	}

	while (!FunctionWorklist.empty()) {
		std::pair<Function *, CallingContext *> &pair = FunctionWorklist.front();
		FunctionWorklist.pop_front();
		UniqueFunctionSet.erase(pair);

		Function *F = pair.first;
		CallingContext *context = pair.second;

		if (skipFunction(*F)) {
			continue;
		}

		errs() << "processing " << F->getName() << "\n";
		analyzeFunction(*F, context);
		errs() << "done processing " << F->getName() << "\n";
		delete context;
		errs() << "context deleted\n";
	}
	errs() << "returning\n";
 	return true;
}

void PMRobustness::analyzeFunction(Function &F, CallingContext *Context) {
#ifdef DUMP_INST_STATE
	if (shouldDebug(&F)) {
		F.dump();
		errs() << "Analyzing Function " << F.getName() << " with Context: \n";
		Context->dump();
	}
#endif

	state_map_t *AbsState = &AbstractStates[&F];
	b_state_map_t *BlockAbsState = &BlockEndAbstractStates[&F];

	DenseMap<BasicBlock *, addr_set_t> &ArraySets = UnflushedArrays[&F];
	StmtErrorSet = &FunctionStmtErrorSets[&F];

#ifdef INTERPROCEDURAL
	CurrentContext = Context;
	FunctionArguments.clear();
	unsigned i = 0;
	for (Function::arg_iterator it = F.arg_begin(); it != F.arg_end(); it++) {
		FunctionArguments[&*it] = i++;
	}

	// Check if two or more parameters are unsafe (i.e. escaped and dirty/clwb)
	HasTwoUnsafeParams = false;
	bool has_unsafe_objs = false;
	for (unsigned i = 0; i < F.arg_size(); i++) {
		ParamState &PS = Context->getState(i);
		if (PS.isEscaped() && (PS.isDirty() || PS.isClwb())) {
			if (has_unsafe_objs) {
				HasTwoUnsafeParams = true;
				break;
			}

			has_unsafe_objs = true;
		}
	}
#endif

	// Collect all return statements of Function F
	SmallPtrSet<Instruction *, 8> &RetSet = FunctionRetInstMap[&F];
	if (RetSet.empty()) {
		for (BasicBlock &BB : F) {
			if (!BB.getTerminator())
				errs() << "malformed BB: " << BB << "\n";
			if (isa<ReturnInst>(BB.getTerminator()))
				RetSet.insert(BB.getTerminator());
		}
	}

	DenseMap<const BasicBlock *, bool> &fence_analysis = FenceAnalysisMap[&F];
	fence_analysis.clear();


	// LLVM allows duplicate predecessors: https://stackoverflow.com/questions/65157239/llvmpredecessors-could-return-duplicate-basic-block-pointers
	DenseMap<const BasicBlock *, SmallSetVector<BasicBlock *, 8>> block_predecessors;
	DenseMap<const BasicBlock *, SmallSetVector<BasicBlock *, 8>> block_successors;
	FunctionMarksEscDirObj = false;
	visited_blocks.clear();

	// Analyze F
	BlockWorklist.push_back(&F.getEntryBlock());
	while (!BlockWorklist.empty()) {
		BasicBlock *block = BlockWorklist.front();
		BlockWorklist.pop_front();

		BasicBlock::iterator prev = block->begin(), next = block->begin();
		addr_set_t &array_addr_set = ArraySets[block];

		for (BasicBlock::iterator it = block->begin(); it != block->end(); it++) {
			//keep track of next iterator as instructions could be inserted after the current iterator
			state_t * state = &(*AbsState)[&*it];

			// Build state from predecessors' states
			if (it == block->begin()) {
				// First instruction; take the union of predecessors' states
				if (block == &F.getEntryBlock()) {
					// Entry block: has no precedessors
					// Prepare initial state based on parameters
#ifdef INTERPROCEDURAL
					computeInitialState(state, F, Context);
#endif
				} else if (BasicBlock *pred = block->getUniquePredecessor()) {
					// Unique predecessor; copy the state of last instruction and unflushed arrays in the pred block
					state_t * prev_s = &(*AbsState)[pred->getTerminator()];

					// Safety check
					if (!visited_blocks[pred])
						assert(false);

					copyState(prev_s, state);
					copyArrayState(ArraySets[pred], array_addr_set);
					fence_analysis[block] = fence_analysis[pred];
				} else {
					// Multiple predecessors
					SmallSetVector<BasicBlock *, 8> &pred_list = block_predecessors[block];
					if (pred_list.empty()) {
						for (BasicBlock *pred : predecessors(block)) {
							pred_list.insert(pred);
						}
					}

					// Safety check
					bool visited_any = false;
					for (BasicBlock *pred : pred_list) {
						if (visited_blocks[pred]) {
							visited_any = true;
							break;
						}
					}

					if (!visited_any)
						assert(false);
					if (BlockEndFence && FlushInsertMode == OPTIMIZED)
						fenceIfDifferentClwbStates(pred_list, AbsState);
					copyMergedState(AbsState, pred_list, state);
					copyMergedArrayState(ArraySets, pred_list, array_addr_set);

					// Merge the fence_state in predecessors
					bool fence_state = true;
					for (BasicBlock *pred: pred_list) {
						fence_state &= fence_analysis[pred];
					}
					fence_analysis[block] = fence_state;
				}
			} else {
				// Copy the previous instruction's state
				copyState(&(*AbsState)[&*prev], state);
			}
			processInstruction(state, &*it);

			prev = it;
		} // End of basic block instruction iteration

		// Copy block terminator's state and check if it has changed
		state_t *terminator_state = &(*AbsState)[block->getTerminator()];
		state_t *block_end_state = &(*BlockAbsState)[block];
#ifdef DUMP_BLOCK_STATE
		if (shouldDebug(&F) && shouldDebug(block)) {
			errs() << "------ Block " << block->getName() << " end state before------\n";
			printMap(block_end_state);
		}
#endif
		bool block_state_changed = copyStateCheckDiff(terminator_state, block_end_state);
#ifdef DUMP_BLOCK_STATE
		if (shouldDebug(&F) && shouldDebug(block)) {
			errs() << "------- After ------\n";
			printMap(block_end_state);
		}
#endif

		// Push block successors to BlockWorklist if block state has changed
		// or it is the first time we visit this block
		if (block_state_changed || !visited_blocks[block]) {
			visited_blocks[block] = true;

			SmallSetVector<BasicBlock *, 8> &succ_list = block_successors[block];
			if (succ_list.empty()) {
				for (BasicBlock *succ : successors(block)) {
					succ_list.insert(succ);
				}
			}

			for (BasicBlock *succ : succ_list) {
				BlockWorklist.push_back(succ);
			}
		}
	}

#ifdef INTERPROCEDURAL
	// Only verify if output states have been changed
	bool state_changed = computeFinalState(AbsState, F, Context);
	if (state_changed) {
		// push callers with their contexts
		SetVector<std::pair<Function *, CallingContext *>> &Callers = FunctionCallerMap[&F];
		for (const std::pair<Function *, CallingContext *> &C : Callers) {
			if (UniqueFunctionSet.find(C) == UniqueFunctionSet.end()) {
				// Not found in FunctionWorklist
				Function *Function = C.first;
				CallingContext *CallerContext = new CallingContext(C.second);
				FunctionWorklist.emplace_back(Function, CallerContext);
				UniqueFunctionSet.insert(std::make_pair(Function, CallerContext));

				//errs() << "(LOG4) Function " << Function->getName() << " added to worklist in " << F.getName() << "\n";
			}
		}
	}
#endif
}

// DenseMap<Value *, ob_state_t *> state_t;
void PMRobustness::copyState(state_t * src, state_t * dst) {
	// Mark each item in dst as `to delete`; they are unmarked if src contains them
	for (state_t::iterator it = dst->begin(); it != dst->end(); it++)
		it->second->markDelete();

	for (state_t::iterator it = src->begin(); it != src->end(); it++) {
		ob_state_t *object_state = dst->lookup(it->first);
		if (object_state == NULL) {
			object_state = new ob_state_t(it->second);
			(*dst)[it->first] = object_state;
		} else {
//			if (object_state->size != it->second->size) {
//				errs() << "dst size: " << object_state->size << "\t";
//				errs() << "src size: " << it->second->size << "\n";
//			}
			object_state->copyFrom(it->second);
			object_state->unmarkDelete();
		}
	}

	// Remove items not contained in src
	for (state_t::iterator it = dst->begin(); it != dst->end(); it++) {
		if (it->second->shouldDelete()) {
			delete it->second;
			dst->erase(it);
		}
	}
}

void PMRobustness::copyArrayState(addr_set_t &src, addr_set_t &dst) {
	for (addr_set_t::iterator it = src.begin(); it != src.end(); it++) {
		ArrayInfo &info = dst[it->first];
		info.copyFrom(it->second);
	}
}

bool PMRobustness::copyStateCheckDiff(state_t * src, state_t * dst) {
	bool updated = false;

	// Mark each item in dst as `to delete`; they are unmarked if src contains them
	for (state_t::iterator it = dst->begin(); it != dst->end(); it++)
		it->second->markDelete();

	for (state_t::iterator it = src->begin(); it != src->end(); it++) {
		ob_state_t *object_state = dst->lookup(it->first);
		if (object_state == NULL) {
			// mark_delete is initialized to false;
			object_state = new ob_state_t(it->second);
			(*dst)[it->first] = object_state;
			updated = true;
		} else {

#ifdef DUMP_BLOCK_DIFF_STATE
			auto before = *object_state;
#endif
			bool diff = object_state->copyFromCheckDiff(it->second);
#ifdef DUMP_BLOCK_DIFF_STATE
			if (diff) {
				errs() << "------ Val " << *it->first << " state before------\n";
				object_state->dump();
				errs() << "----- After ------\n";
				before.dump();
			}
#endif
			updated |= diff;
			object_state->unmarkDelete();
		}
	}

	// Remove items not contained in src
	for (state_t::iterator it = dst->begin(); it != dst->end(); it++) {
		if (it->second->shouldDelete()) {
			delete it->second;
			dst->erase(it);
			updated = true;
		}
	}

	return updated;
}

void PMRobustness::copyMergedState(state_map_t *AbsState,
		SmallSetVector<BasicBlock *, 8> &src_list, state_t * dst) {
	for (state_t::iterator it = dst->begin(); it != dst->end(); it++) {
		it->second->setSize(0);
		it->second->markDelete();
	}

	for (BasicBlock *pred : src_list) {
		if (!visited_blocks[pred]) {
			continue;
		}

		state_t *s = &(*AbsState)[pred->getTerminator()];
		//DenseMap<Value *, ob_state_t *> state_t;
		for (state_t::iterator it = s->begin(); it != s->end(); it++) {
			state_t::iterator item = dst->find(it->first);
			if (item != dst->end()) {
				// (Loc, vector<VarState>) pair found
				ob_state_t *A = item->second;
				ob_state_t *B = it->second;

				if (A->getSize() == 0) {
					A->copyFrom(B);
				} else {
					A->mergeFrom(B);
				}

				A->unmarkDelete();
			} else {
				(*dst)[it->first] = new ob_state_t(it->second);
			}
		}
	}

	// Remove items not contained in src
	for (state_t::iterator it = dst->begin(); it != dst->end(); it++) {
		if (it->second->shouldDelete()) {
			delete it->second;
			dst->erase(it);
		}
	}
}

void PMRobustness::copyMergedArrayState(DenseMap<BasicBlock *, addr_set_t> &ArraySets,
		SmallSetVector<BasicBlock *, 8> &src_list, addr_set_t &dst) {
	for (BasicBlock *pred : src_list) {
		if (!visited_blocks[pred]) {
			continue;
		}

		addr_set_t &s = ArraySets[pred];
		//DenseMap<const Value *, ArrayInfo> addr_set_t;
		for (addr_set_t::iterator it = s.begin(); it != s.end(); it++) {
			addr_set_t::iterator item = dst.find(it->first);
			if (item != dst.end()) {
				// (Loc, vector<VarState>) pair found
				ArrayInfo &A = item->second;
				A.mergeFrom(it->second);
			} else {
				ArrayInfo &A = dst[it->first];
				A.copyFrom(it->second);
			}
		}
	}
}

void PMRobustness::processInstruction(state_t * map, Instruction * I) {
#ifdef DUMP_INST_STATE
	if (shouldDebug(I->getFunction()) && shouldDebug(I->getParent())) {
		errs() << "Before " << *I << "\n\n";
		printMap(map);
	}
#endif
	InstructionMarksEscDirObj = false;
	CallMarksEscDirObj = false;
	MultiUnsafeFieldsPrevPos = "";

	bool updated = false;
	bool check_error = false;
	bool non_dirty_escaped_before_call = true;
	bool report_release_error = false;

	if (skipAnnotatedInstruction(I)) {
		return;
	}

	if (I->isAtomic()) {
		processAtomic(map, I, report_release_error);
		check_error = true;
	} else if (isa<LoadInst>(I)) {
		processLoad(map, I);
		//TODO: figure out the performance implication of this 
		//check_error = true;
	} else if (isa<StoreInst>(I)) {
		processStore(map, I);
		check_error = true;
	} else if (isa<PHINode>(I)) {
		processPHI(map, I);
	} else if (isa<SelectInst>(I)) {
		processSelect(map, I);
	} else if (isMutexLock(I)) {
		// mutex lock is usually implemented with RMW; cite the x86 PM semantics paper
		processFence(map, I);
	} else if (isMutexUnlock(I)) {
		processMutexUnlock(map, I);
		report_release_error = true;
	} else if (isa<CallInst>(I) || isa<InvokeInst>(I)) {

		// Ignore Debug info Instrinsics
		if (isa<DbgInfoIntrinsic>(I)) {
			return;
		} else if (isa<MemIntrinsic>(I)) {
			processMemIntrinsic(map, I);
			check_error = true;
		} else if (isInFunctionAnnotation(I)) {
			processInFunctionAnnotation(I);
		} else if (isFunctionAnnotated(I)) {
			processAnnotatedFunction(map, I, check_error);
		} else {
			NVMOP op = whichNVMoperation(I);
			if (op == NVM_FENCE) {
				// TODO: fence operations
				processFence(map, I);
			} else if (op == NVM_CLWB || op == NVM_CLFLUSH) {
				processFlush(map, I, op);
			} else {
#ifdef INTERPROCEDURAL
				processCalls(map, I, non_dirty_escaped_before_call, report_release_error);
				check_error = true;
#endif
			}
		}
	}

	if (check_error) {
		checkMultiObjError(map, I, non_dirty_escaped_before_call);
	}

	if (report_release_error) {
		checkReleaseError(map, I);
	}

	if (!MultiUnsafeFieldsPrevPos.empty()) {
		reportMultipleEscDirtyFieldsError(map, I);
	}

#ifdef DUMP_INST_STATE
	if (shouldDebug(I->getFunction()) && shouldDebug(I->getParent())) {
		errs() << "After " << *I << "\n\n";
		printMap(map);
	}
#endif
}

bool PMRobustness::processAtomic(state_t * map, Instruction * I, bool &report_release_error) {
	bool updated = false;
	const DataLayout &DL = I->getModule()->getDataLayout();

	int atomic_order_index = -1;
	Value *Addr = NULL;
	if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
		atomic_order_index = getAtomicOrderIndex(LI->getOrdering());
		Addr = LI->getPointerOperand();

		//errs() << "(LOG1 Load): atomic index: " << atomic_order_index << "\n";
	} else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
		atomic_order_index = getAtomicOrderIndex(SI->getOrdering());
		Addr = SI->getPointerOperand();

		//errs() << "(LOG2 Store): atomic index: " << atomic_order_index << "\n";
	} else if (AtomicRMWInst *RMWI = dyn_cast<AtomicRMWInst>(I)) {
		atomic_order_index = getAtomicOrderIndex(RMWI->getOrdering());
		Addr = RMWI->getPointerOperand();

		//errs() << "(LOG3 RMW): atomic index: " << atomic_order_index << "\n";
	} else if (AtomicCmpXchgInst *CASI = dyn_cast<AtomicCmpXchgInst>(I)) {
		atomic_order_index = getAtomicOrderIndex(CASI->getSuccessOrdering());
		Addr = CASI->getPointerOperand();

		//errs() << "(LOG4 CAS): atomic index: " << atomic_order_index << "\n";
	} else if (FenceInst *FI = dyn_cast<FenceInst>(I)) {
		atomic_order_index = getAtomicOrderIndex(FI->getOrdering());
		//errs() << "(LOG5 Fence): atomic index: " << atomic_order_index << "\n";
	}

	// Set release_op flag for fence and other release or stronger operations
	if ((isa<FenceInst>(I) || !isPMAddr(I->getFunction(), Addr, DL)) &&
		(atomic_order_index == (int)AtomicOrderingCABI::release || 
		(FlushInsertMode == NO_FLUSH && atomic_order_index == (int)AtomicOrderingCABI::seq_cst))) {
		//errs() << "Non PM Atomic operation detected for: " << *I << "\n";
		//I->getFunction()->dump();

		FunctionSummary *FS = getOrCreateFunctionSummary(I->getFunction());
		FS->setRelease();
		//errs() << "Set Release Instruction: " << *I << "\n";
		//errs() << "For " << I->getFunction()->getName() << "\n";
		report_release_error = true;
	}

	if (isa<AtomicRMWInst>(I) || isa<AtomicCmpXchgInst>(I) || isa<FenceInst>(I)) 
		processFence(map, I);

	if (isa<StoreInst>(I)) {
		updated |= processStore(map, I);
		if (atomic_order_index == (int)AtomicOrderingCABI::seq_cst)
			processFence(map, I);
	} else if (isa<LoadInst>(I)) {
		updated |= processLoad(map, I);
	} else if (AtomicRMWInst *RMWI = dyn_cast<AtomicRMWInst>(I)) {
		// Treat atomic RMWs as load + store
		updated |= processLoad(map, I);
		updated |= processStore(map, I);
		//errs() << "Atomic RMW processed\n";
	} else if (AtomicCmpXchgInst *CASI = dyn_cast<AtomicCmpXchgInst>(I)) {
		// FIXME: Treat CAS as RMW for now
		updated |= processLoad(map, I);
		updated |= processStore(map, I);
	}

	return updated;
}

bool PMRobustness::processMemIntrinsic(state_t * map, Instruction * I) {
	auto *MI = cast<MemIntrinsic>(I);
	auto Addr = MI->getRawDest();
	auto Size = MI->getLength();
	auto &DL = I->getModule()->getDataLayout();
		if (!isPMAddr(I->getFunction(), Addr, DL))
		return false;


	DecomposedGEP DecompGEP;
	decomposeAddress(DecompGEP, Addr, DL);
	unsigned offset = DecompGEP.getOffsets();

	if (DecompGEP.isArray || offset == UNKNOWNOFFSET || offset == VARIABLEOFFSET) {
		ob_state_t *object_state = getObjectState(map, DecompGEP.Base);
		object_state->setToArray();
	}
	if (checkPointerArithmetics(Addr, DL)) {
		if (StmtErrorSet->find(I) == StmtErrorSet->end()) {
			StmtErrorSet->insert(I);

			errs() << "Warning: Memcpy to addresses computed by pointer arithmetics: ";
			getPosition(I, true);
			errs() << "@@ Instruction " << *I << "\n";
			if (FlushInsertMode == OPTIMIZED) {
					MDNode *N = MDNode::get(*Ctx, None);
				auto fence = fenceAndChangeState(I, map);
				fence->setMetadata(PTR_ARITH_FENCE, N);
			} 
		}

		return false;
	}

	//unsigned TypeSize = getMemoryAccessSize(Addr, DL);
	ob_state_t *object_state = getObjectState(map, DecompGEP.Base);
	unsigned size;
	if (isa<ConstantInt>(Size))
		size = cast<ConstantInt>(Size)->getZExtValue();
	else {
		// size could be a variable; see ulog.c:329
		// TODO: How to overapproximate size?
		size = object_state->getSize() > offset ? 
			object_state->getSize() - offset : 1;
	}
	
	//bool has_other_nonclean_bytes = object_state->hasNoncleanBytesNotIn(offset, size);
	//if (has_other_nonclean_bytes && object_state->isEscaped()) {
	//	MultiUnsafeFieldsPrevPos = object_state->getDirtyEscapedPosStr();
	//}
	object_state->setDirty(offset, size, I);
	if (object_state->isEscaped()) {
		InstructionMarksEscDirObj = true;
		FunctionMarksEscDirObj = true;
	}
	

	return false;	
}

bool PMRobustness::processStore(state_t * map, Instruction * I) {
	bool updated = false;
	IRBuilder<> IRB(I);
	const DataLayout &DL = I->getModule()->getDataLayout();
	Value *Addr = NULL;
	Value *Val = NULL;

	if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
		Addr = SI->getPointerOperand();
		Val = SI->getValueOperand();
	} else if (AtomicRMWInst *RMWI = dyn_cast<AtomicRMWInst>(I)) {
		Addr = RMWI->getPointerOperand();

		// Rule 2.1 only makes sense for atomic_exchange
		if (RMWI->getOperation() == AtomicRMWInst::Xchg)
			Val = RMWI->getValOperand();
	} else if (AtomicCmpXchgInst *CASI = dyn_cast<AtomicCmpXchgInst>(I)) {
		Addr = CASI->getPointerOperand();
		Val = CASI->getNewValOperand();
	} else {
		return false;
	}

	DecomposedGEP DecompGEP;
	decomposeAddress(DecompGEP, Addr, DL);
	unsigned offset = DecompGEP.getOffsets();

	if (DecompGEP.isArray || offset == UNKNOWNOFFSET || offset == VARIABLEOFFSET) {
		if (isPMAddr(I->getFunction(), DecompGEP.Base, DL) ||
			isPMAddr(I->getFunction(), Addr, DL)) {
			ob_state_t *object_state = getObjectState(map, DecompGEP.Base);
			object_state->setToArray();
		}
	}
	if (isPMAddr(I->getFunction(), Addr, DL)) {
			// Report warnings for addresses computed by pointer arithmetics
		if (checkPointerArithmetics(Addr, DL)) {
			if (StmtErrorSet->find(I) == StmtErrorSet->end()) {
				StmtErrorSet->insert(I);

				errs() << "Warning: Store to addresses computed by pointer arithmetics: ";
				IRBuilder<> IRB(I);
				getPosition(I, true);
				errs() << "@@ Instruction " << *I << "\n";
			if (FlushInsertMode == OPTIMIZED) {
					MDNode *N = MDNode::get(*Ctx, None);
				auto fence = fenceAndChangeState(I, map);
				fence->setMetadata(PTR_ARITH_FENCE, N);
			} 
			}

			return false;
		}

		// Rule 1: x.f = v => x.f becomes dirty
		unsigned TypeSize = getMemoryAccessSize(Addr, DL);
		ob_state_t *object_state = getObjectState(map, DecompGEP.Base, updated);

		bool has_other_nonclean_bytes = object_state->hasNoncleanBytesNotIn(offset, TypeSize);
		if (has_other_nonclean_bytes && object_state->isEscaped()) {
			MultiUnsafeFieldsPrevPos = object_state->getDirtyEscapedPosStr();
		}
		updated |= object_state->setDirty(offset, TypeSize, I);
		// For reporting in-function error
		if (object_state->isEscaped()) {
			InstructionMarksEscDirObj = true;
			FunctionMarksEscDirObj = true;
		}
	}

	// Rule 2.1: *x = p => all fields of p escapes
	// Val(i.e. p) should be PM Addr
	if (Val && Val->getType()->isPointerTy() && isPMAddr(I->getFunction(), Val, DL)) {
		DecomposedGEP ValDecompGEP;
		decomposeAddress(ValDecompGEP, Val, DL);
		unsigned offset = ValDecompGEP.getOffsets();

		if (ValDecompGEP.isArray || offset == UNKNOWNOFFSET || offset == VARIABLEOFFSET) {
			ob_state_t *object_state = getObjectState(map, ValDecompGEP.Base, updated);

			// Mark it as escaped
			updated |= object_state->setEscape(I);
		} else {
			ob_state_t *object_state = getObjectState(map, ValDecompGEP.Base, updated);

			// Note: if *x = &p->f, then *p is potentially reachabled; so mark it as escaped
			bool changed_to_escaped = object_state->setEscape(I);
			updated |= changed_to_escaped;

			assert(object_state);
			// For reporting in-function error
			if (changed_to_escaped && (object_state->isDirty() || object_state->isClwb())) {
				InstructionMarksEscDirObj = true;
				FunctionMarksEscDirObj = true;
			}
		}
	}
	

	return updated;
}

bool PMRobustness::processLoad(state_t * map, Instruction * I) {
	bool updated = false;
	IRBuilder<> IRB(I);
	const DataLayout &DL = I->getModule()->getDataLayout();
	Value *Addr = NULL;

	if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
		Addr = LI->getPointerOperand();
	} else if (AtomicRMWInst *RMWI = dyn_cast<AtomicRMWInst>(I)) {
		Addr = RMWI->getPointerOperand();
	} else if (AtomicCmpXchgInst *CASI = dyn_cast<AtomicCmpXchgInst>(I)) {
		Addr = CASI->getPointerOperand();
	} else {
		return false;
	}

	DecomposedGEP DecompGEP;
	decomposeAddress(DecompGEP, Addr, DL);
	unsigned offset = DecompGEP.getOffsets();

	if (DecompGEP.isArray || offset == UNKNOWNOFFSET || offset == VARIABLEOFFSET) {
		if (isPMAddr(I->getFunction(), DecompGEP.Base, DL) ||
			isPMAddr(I->getFunction(), Addr, DL)) {
			if (I->isAtomic() && isa<LoadInst>(I)) {
				ob_state_t *object_state = getObjectState(map, DecompGEP.Base);
				object_state->setToArray();
			}
		}

		//errs() << *I << "\n";
		//getPosition(I, true);
	}
	if (checkPointerArithmetics(Addr, DL)) {
		// Only need to check for atomic loads
		if (I->isAtomic() && isa<LoadInst>(I)) {
			if (StmtErrorSet->find(I) == StmtErrorSet->end()) {
				StmtErrorSet->insert(I);
	
				errs() << "Warning: Load from addresses computed by pointer arithmetics: ";
				getPosition(I, true);
				errs() << "@@ Instruction " << *I << "\n";
			}
		}
	
		return false;
	}
	
	if (isPMAddr(I->getFunction(), Addr, DL)) {
		if (I->isAtomic() && isa<LoadInst>(I)) {
			// Mark the address as dirty to detect interthread robustness violation
			// For Atomic RMW, this is already done in processStore
			ob_state_t *object_state = getObjectState(map, DecompGEP.Base);
			unsigned TypeSize = getMemoryAccessSize(Addr, DL);
	
			//bool has_other_nonclean_bytes = object_state->hasNoncleanBytesNotIn(offset, TypeSize);
			//if (has_other_nonclean_bytes && object_state->isEscaped()) {
			//	//errs() << "(LOGN) check range: [" << offset << ", " << offset + TypeSize << ")\n";
			//	//errs() << *I << "\n";
			//	MultiUnsafeFieldsPrevPos = object_state->getDirtyEscapedPosStr();
			//}
			if (!Flit)
				updated |= object_state->setDirty(offset, TypeSize, I);
			// For reporting in-function error
			if (object_state->isEscaped()) {
				InstructionMarksEscDirObj = true;
				FunctionMarksEscDirObj = true;
			}
		}
	}
	// Rule 2.2: p = *x => p escapes
	if (I->getType()->isPointerTy() && isPMAddr(I->getFunction(), I, DL)) {
		DecomposedGEP LIDecompGEP;
		decomposeAddress(LIDecompGEP, I, DL);
		unsigned offset = LIDecompGEP.getOffsets();
	
		if (LIDecompGEP.isArray) {
			assert(false && "Fix me");
		} else if (offset > 0) {
			assert(false && "fix me");
		}
	
		//unsigned TypeSize = getMemoryAccessSize(Addr, DL);
		ob_state_t *object_state = getObjectState(map, LIDecompGEP.Base, updated);
		bool changed_to_escaped = object_state->setEscape(I);
		updated |= changed_to_escaped;
	
		// For reporting in-function error
		if (changed_to_escaped && object_state->isDirty()) {
			InstructionMarksEscDirObj = true;
			FunctionMarksEscDirObj = true;
		}
	}


	return updated;
}

bool PMRobustness::processPHI(state_t * map, Instruction * I) {
	bool updated = false;
	IRBuilder<> IRB(I);
	const DataLayout &DL = I->getModule()->getDataLayout();

	if (!I->getType()->isPointerTy())
		return false;

	ob_state_t *phi_state = NULL;
	bool first_state = true;

	PHINode *PHI = cast<PHINode>(I);
	//computeAliasSet(PHI);

	for (unsigned i = 0; i != PHI->getNumIncomingValues(); i++) {
		Value *V = PHI->getIncomingValue(i);
		if (!visited_blocks[PHI->getIncomingBlock(i)]) {
			continue;
		}

		DecomposedGEP DecompGEP;
		decomposeAddress(DecompGEP, V, DL);
		unsigned offset = DecompGEP.getOffsets();

		if (DecompGEP.isArray || offset == UNKNOWNOFFSET || offset == VARIABLEOFFSET) {
			continue;
		} else {
			ob_state_t *object_state = map->lookup(DecompGEP.Base);
			if (object_state == NULL)
				continue;

			if (first_state) {
				phi_state = getObjectState(map, I);
				phi_state->copyFrom(object_state);
				phi_state->resetDirtyEscapedPos(nullptr);
				first_state = false;
			} else {
				// FIXME: only need to merge some field, not the entire object
				phi_state->mergeFrom(object_state);
			}
		}
	}

	return updated;
}

bool PMRobustness::processSelect(state_t * map, Instruction * I) {
	bool updated = false;
	IRBuilder<> IRB(I);
	const DataLayout &DL = I->getModule()->getDataLayout();

	if (!I->getType()->isPointerTy())
		return false;

	ob_state_t *state = NULL;
	bool first_state = true;

	unsigned i = 0;
	for (User::op_iterator it = I->op_begin(); it != I->op_end(); it++, i++) {
		// There are three operands in total. Skip the first operand
		if (i == 0)
			continue;

		Value *V = *it;

		DecomposedGEP DecompGEP;
		decomposeAddress(DecompGEP, V, DL);
		unsigned offset = DecompGEP.getOffsets();

		if (DecompGEP.isArray || offset == UNKNOWNOFFSET || offset == VARIABLEOFFSET) {
			continue;
		} else {
			ob_state_t *object_state = map->lookup(DecompGEP.Base);
			if (object_state == NULL)
				continue;

			if (first_state) {
				state = getObjectState(map, I);
				state ->copyFrom(object_state);
				first_state = false;
			} else {
				// FIXME: only need to merge some field, not the entire object
				state->mergeFrom(object_state);
			}
		}
	}

	return updated;
}

void PMRobustness::processMutexUnlock(state_t *map, Instruction *I) {
	//errs() << "pthread_mutex_unlock detected in function: " << I->getFunction()->getName() << "\n";

	FunctionSummary *FS = getOrCreateFunctionSummary(I->getFunction());
	FS->setRelease();
	//errs() << "Set Release Instruction: " << *I << "\n";
	//errs() << "For " << I->getFunction()->getName() << "\n";
}

bool PMRobustness::processFence(state_t *map, Instruction *I) {
	DenseMap<const BasicBlock *, bool> &fence_analysis = FenceAnalysisMap[I->getFunction()];
	fence_analysis[I->getParent()] = true;
	bool updated = false;

	for (state_t::iterator it = map->begin(); it != map->end(); it++) {
		ob_state_t *object_state = it->second;
		updated |= object_state->applyFence();
	}

	// Handle unflushed array addresses
	DenseMap<BasicBlock *, addr_set_t> &ArraySets = UnflushedArrays[I->getFunction()];
	addr_set_t &unflushed_addr = ArraySets[I->getParent()];

	if (unflushed_addr.empty())
		return updated;

	std::vector<const Value *> to_erase;
	for (addr_set_t::iterator it = unflushed_addr.begin(); it != unflushed_addr.end(); it++) {
		ParamStateType s = it->second.getState();
		if (s == ParamStateType::CLWB_ESCAPED)
			to_erase.push_back(&*it->first);

		// Array element states shall all be marked as ESCAPED
		assert(s != ParamStateType::DIRTY_CAPTURED && s != ParamStateType::CLWB_CAPTURED);
	}

	for (const Value *addr: to_erase) {
		unflushed_addr.erase(addr);
	}

	return updated;
}

void PMRobustness::processInFunctionAnnotation(Instruction *I) {
	CallBase *CB = cast<CallBase>(I);
	Function *callee = CB->getCalledFunction();

	// Ignore code blocked enclosed by pm_ignore_block_begin() and pm_ignore_block_end()
	if (callee->getName() == "pm_ignore_block_begin") {
		bool annotate = false;
		std::list<BasicBlock *> worklist;
		SmallSetVector<BasicBlock *, 8> seen;
		worklist.push_back(I->getParent());
		MDNode *N = MDNode::get(*Ctx, None);

		while (!worklist.empty()) {
			BasicBlock *cur = worklist.front();
			worklist.pop_front();
			bool break_in_the_middle = false;

			for (BasicBlock::iterator it = cur->begin(); it != cur->end();) {
				auto curI = &*it;
				it++;
				if (annotate) {
					curI->setMetadata(IGNORE, N);
				}

				if (curI == I) {
					// Start annotating after "pm_ignore_block_begin"
					annotate = true;
					curI->eraseFromParent();
				} else if (CallBase *CB = dyn_cast<CallBase>(curI)) {
					if (Function *callee = CB->getCalledFunction()) {
						if (callee->getName() == "pm_ignore_block_end") {
							// Stop annotating instructions in this block
							break_in_the_middle = true;
							curI->eraseFromParent();
							break;
						}
					}
				}
			}

			// Add successors unless seeing "pm_ignore_block_end"
			if (!break_in_the_middle) {
				for (BasicBlock *succ : successors(cur)) {
					if (seen.insert(succ))
						worklist.push_back(succ);
				}
			}
		}
	}
}


void PMRobustness::processFlush(state_t *map, Instruction *I, NVMOP op) {
	assert(op == NVM_CLFLUSH || op == NVM_CLWB);
	CallInst *callInst = cast<CallInst>(I);
	auto *Addr = callInst->getArgOperand(0);
	const DataLayout &DL = I->getModule()->getDataLayout();
	DecomposedGEP DecompGEP;
	decomposeAddress(DecompGEP, Addr, DL);
	ob_state_t *object_state = map->lookup(DecompGEP.Base);

	unsigned offset = DecompGEP.getOffsets();

	if (object_state == NULL) {
		// TODO: to be solve in interprocedural analysis
		// public method calls can modify the state of objects e.g. masstress.cpp:320
		//errs() << "ProcessFlush: Flush an unknown address " << *DecompGEP.Base << "\n";
		//assert(false && "Flush an unknown address");
	} else {
		unsigned size = FLUSH_SIZE;
		//errs() << "flush " << *DecompGEP.Base << " at " << offset << " for " << size << " bytes with "  << *I << "\n";
		if (op == NVM_CLFLUSH)
			object_state->setFlush(offset, size);
		else if (op == NVM_CLWB)
			object_state->setClwb(offset, size);
	}
	
}

bool PMRobustness::processAnnotatedFunction(state_t *map, Instruction *I, bool &check_error) {
	CallBase *CB = cast<CallBase>(I);
	Function *callee = CB->getCalledFunction();
	bool updated = false;

	if (callee->hasFnAttribute("ignore") || callee->hasFnAttribute("preprocess_ignore") || callee->hasFnAttribute("suppress")) {
		// do nothing
	} else if (callee->hasFnAttribute("myflush")) {
		updated = true;
		processFlushWrapperFunction(map, I);
	} else if (callee->hasFnAttribute("flush_parameter")) {
		updated = true;
		processFlushParameterFunction(map, I);
	} else if (callee->hasFnAttribute("return")) {
		updated = true;
		processReturnAnnotation(map, I);
	} else if (callee->hasFnAttribute("persist_memcpy")) {
		updated = true;
		check_error = true;
		processPMMemcpy(map, I);
	} else {
		assert(false && "Unknown annotated function");
	}

	return updated;
}

void PMRobustness::processFlushWrapperFunction(state_t * map, Instruction * I) {
	CallBase *callInst = cast<CallBase>(I);
	const DataLayout &DL = I->getModule()->getDataLayout();
	Function *callee = callInst->getCalledFunction();
	assert(callee);

	std::vector<StringRef> annotations;
	getAnnotatedParamaters("myflush", annotations, callee);

	Value *Addr = NULL;
	Value *FlushSize = NULL;
	for (unsigned i = 0; i < annotations.size(); i++) {
		StringRef &token = annotations[i];
		if (token == "addr") {
			Addr = callInst->getArgOperand(i);
		} else if (token == "size") {
			FlushSize = callInst->getArgOperand(i);
		} else if (token == "ignore") {
			// Ignore
		} else {
			assert(false && "bad annotation");
		}
	}

	NVMOP FlushOp = NVM_UNKNOWN;
	FlushOp = analyzeFlushType(*callee);
	assert(FlushOp == NVM_CLWB || FlushOp == NVM_CLFLUSH);

/*
	errs() << "flush wrapper " << *Addr << "\n	for " << *FlushSize << "\n	";
	IRBuilder<> IRB(I);
	getPosition(I, true);
	I->getFunction()->dump();
*/
	DecomposedGEP DecompGEP;
	decomposeAddress(DecompGEP, Addr, DL);
	unsigned offset = DecompGEP.getOffsets();
	///errs() << "DecompGEP Base: " << *DecompGEP.Base << ", offset " << offset << ", isArray " << DecompGEP.isArray << "\n";


	ob_state_t *object_state = map->lookup(DecompGEP.Base);
	if (object_state == NULL) {
		// TODO: to be solve in interprocedural analysis
		// public method calls can modify the state of objects e.g. masstress.cpp:320
		errs() << "Flush an unknown address " << *Addr << "\n";
		//assert(false && "Flush an unknown address");
	} else {
		unsigned size;
		if (isa<ConstantInt>(FlushSize))
			size = cast<ConstantInt>(FlushSize)->getZExtValue();
		else {
			// FIXME: flush size can be a variable, such as `sizeof(leafvalue) + len`
			size = object_state->getSize();
		}

		//errs() << "flush " << *DecompGEP.Base << " from " << offset << " to " << size << "\n";
		if (FlushOp == NVM_CLFLUSH)
			object_state->setFlush(offset, size, true);
		else if (FlushOp == NVM_CLWB)
			object_state->setClwb(offset, size, true);
	}
	
}

void PMRobustness::processFlushParameterFunction(state_t * map, Instruction * I) {
	CallBase *callInst = cast<CallBase>(I);
	const DataLayout &DL = I->getModule()->getDataLayout();
	Function *callee = callInst->getCalledFunction();
	assert(callee);

	std::vector<StringRef> annotations;
	getAnnotatedParamaters("flush_parameter", annotations, callee);

	Value *Addr = NULL;
	for (unsigned i = 0; i < annotations.size(); i++) {
		StringRef &token = annotations[i];
		if (token == "addr") {
			Addr = callInst->getArgOperand(i);
		} else if (token == "ignore") {
			// Ignore
		} else {
			assert(false && "bad annotation");
		}
	}

	NVMOP FlushOp = NVM_UNKNOWN;
	FlushOp = analyzeFlushType(*callee);
	assert(FlushOp == NVM_CLWB || FlushOp == NVM_CLFLUSH);

/*
	errs() << "flush wrapper " << *Addr << "\n";
	IRBuilder<> IRB(I);
	getPosition(I, true);
	I->getFunction()->dump();
*/
	DecomposedGEP DecompGEP;
	decomposeAddress(DecompGEP, Addr, DL);
	unsigned offset = DecompGEP.getOffsets();

	ob_state_t *object_state = map->lookup(DecompGEP.Base);
	if (object_state == NULL) {
		// TODO: to be solve in interprocedural analysis
		// public method calls can modify the state of objects e.g. masstress.cpp:320
		errs() << "Flush an unknown address\n";
	} else {
		unsigned size = object_state->getSize();
		if (FlushOp == NVM_CLFLUSH)
			object_state->setFlush(offset, size, true);
		else if (FlushOp == NVM_CLWB)
			object_state->setClwb(offset, size, true);
	}
	
}

void PMRobustness::processReturnAnnotation(state_t * map, Instruction * I) {
	CallBase *callInst = cast<CallBase>(I);
	const DataLayout &DL = I->getModule()->getDataLayout();
	Function *callee = callInst->getCalledFunction();
	assert(callee);

	std::vector<StringRef> annotations;
	getAnnotatedParamaters("return", annotations, callee);

	StringRef &annotation = annotations[0];

	DecomposedGEP DecompGEP;
	decomposeAddress(DecompGEP, I, DL);
	unsigned offset = DecompGEP.getOffsets();

	if (DecompGEP.isArray || offset == UNKNOWNOFFSET || offset == VARIABLEOFFSET) {
		assert(false);
	} else {
		ob_state_t *object_state = getObjectState(map, DecompGEP.Base);
		if (annotation == "escaped") {
			object_state->setEscape(I);
		} else {
			assert(false);
		}
	}
}

void PMRobustness::processPMMemcpy(state_t * map, Instruction * I) {
	CallBase *callInst = cast<CallBase>(I);
	const DataLayout &DL = I->getModule()->getDataLayout();
	Function *callee = callInst->getCalledFunction();
	assert(callee);

	std::vector<StringRef> annotations;
	getAnnotatedParamaters("persist_memcpy", annotations, callee);

	Value *Addr = NULL;
	Value *Size = NULL;
	for (unsigned i = 0; i < annotations.size(); i++) {
		StringRef &token = annotations[i];
		if (token == "addr") {
			Addr = callInst->getArgOperand(i);
		} else if (token == "size") {
			Size = callInst->getArgOperand(i);
		} else if (token == "ignore") {
			// Ignore
		} else {
			assert(false && "bad annotation");
		}
	}

	if (!isPMAddr(I->getFunction(), Addr, I->getModule()->getDataLayout()))
		return;

	DecomposedGEP DecompGEP;
	decomposeAddress(DecompGEP, Addr, DL);
	unsigned offset = DecompGEP.getOffsets();

	if (DecompGEP.isArray || offset == UNKNOWNOFFSET || offset == VARIABLEOFFSET) {
		ob_state_t *object_state = getObjectState(map, DecompGEP.Base);
		object_state->setToArray();
	}
	if (checkPointerArithmetics(Addr, DL)) {
		if (StmtErrorSet->find(I) == StmtErrorSet->end()) {
			StmtErrorSet->insert(I);

			errs() << "Warning: Memcpy to addresses computed by pointer arithmetics: ";
			getPosition(I, true);
			errs() << "@@ Instruction " << *I << "\n";
			if (FlushInsertMode == OPTIMIZED) {
					MDNode *N = MDNode::get(*Ctx, None);
				auto fence = fenceAndChangeState(I, map);
				fence->setMetadata(PTR_ARITH_FENCE, N);
			} 
		}

		return;
	}

	//unsigned TypeSize = getMemoryAccessSize(Addr, DL);
	ob_state_t *object_state = getObjectState(map, DecompGEP.Base);
	unsigned size;
	if (isa<ConstantInt>(Size))
		size = cast<ConstantInt>(Size)->getZExtValue();
	else {
		// size could be a variable; see ulog.c:329
		// TODO: How to overapproximate size?
		size = object_state->getSize() > offset ? 
			object_state->getSize() - offset : 1;
	}
	
	bool has_other_nonclean_bytes = object_state->hasNoncleanBytesNotIn(offset, size);
	if (has_other_nonclean_bytes && object_state->isEscaped()) {
		MultiUnsafeFieldsPrevPos = object_state->getDirtyEscapedPosStr();
	}
	object_state->setDirty(offset, size, I);
	if (object_state->isEscaped()) {
		InstructionMarksEscDirObj = true;
		FunctionMarksEscDirObj = true;
	}
	
}

void PMRobustness::processCalls(state_t *map, Instruction *I, bool &non_dirty_escaped_before, bool &report_release_error) {
	CallBase *CB = cast<CallBase>(I);
	if (CallInst *CI = dyn_cast<CallInst>(CB)) {
		if (CI->isInlineAsm())
			return;
	}

	Function *F = CB->getCalledFunction();
	if (F == NULL) {
		// TODO: why this happens?
		//assert(false);
		return;
	}

	if (F->isVarArg()) {
#ifdef PMROBUST_DEBUG
		errs() << "Cannot handle variable argument functions for " << F->getName() << "\n";
#endif
		return;
	} else if (F->isDeclaration()) {
		// TODO: think about how to approximate calls to functions with no body
#ifdef PMROBUST_DEBUG
		errs() << "Cannot handle functions with no function body: " << F->getName() << "\n";
#endif
		return;
	}

	// Update FunctionCallerMap
	SetVector<std::pair<Function *, CallingContext *>> &Callers = FunctionCallerMap[F];
	if (Callers.count(std::make_pair(CB->getCaller(), CurrentContext)) == 0) {
		// If Caller w/ Context is not found
		CallingContext *ContextCopy = new CallingContext(CurrentContext);
		Callers.insert(std::make_pair(CB->getCaller(), ContextCopy));
	}

	CallingContext *context = computeContext(map, I);
	lookupFunctionResult(map, CB, context, non_dirty_escaped_before, report_release_error);
}

void PMRobustness::getAnnotatedParamaters(std::string attr, std::vector<StringRef> &annotations, Function *callee) {
	StringRef AttrValue = callee->getFnAttribute(attr).getValueAsString();
	std::pair<StringRef, StringRef> Split = AttrValue.split("|");
	annotations.push_back(Split.first);

	while (!Split.second.empty()) {
		Split = Split.second.split("|");
		annotations.push_back(Split.first);
	}

	assert(callee->arg_size() == annotations.size() &&
		"annotations should match the number of paramaters");
}

unsigned PMRobustness::getMemoryAccessSize(Value *Addr, const DataLayout &DL) {
	Type *OrigPtrTy = Addr->getType();
	Type *OrigTy = cast<PointerType>(OrigPtrTy)->getElementType();
	assert(OrigTy->isSized());
	unsigned TypeSize = DL.getTypeStoreSizeInBits(OrigTy);
	if (TypeSize % 8 != 0) {
		//NumAccessesWithBadSize++;
		// Ignore all unusual sizes.
		assert(false && "Bad size access\n");
	}

	return TypeSize / 8;
}

unsigned PMRobustness::getFieldSize(Value *Addr, const DataLayout &DL) {
	Type *OrigPtrTy = Addr->getType();
	Type *OrigTy = cast<PointerType>(OrigPtrTy)->getElementType();
	if (!OrigTy->isSized()) {
		return -1;
	}

	unsigned TypeSize = DL.getTypeStoreSizeInBits(OrigTy);

	return TypeSize / 8;
}


void PMRobustness::getAnalysisUsage(AnalysisUsage &AU) const {
	AU.addRequiredTransitive<AAResultsWrapperPass>();
	AU.addRequiredTransitive<MemoryDependenceWrapperPass>();
	AU.addRequired<CFLAndersTaintWrapperPass>();
	AU.setPreservesAll();
}

bool PMRobustness::skipAnnotatedInstruction(Instruction *I) {
	return I->getMetadata(IGNORE) != NULL;
}

bool PMRobustness::skipFunction(Function &F) {
	return isFunctionAnnotated(F);
}

bool PMRobustness::isPMAddr(const Function *F, const Value * Addr, const DataLayout &DL) {
	DenseSet<Value *> * PMAddrs = NULL;
	if (PMAddrSets.find(F) != PMAddrSets.end()) {
		PMAddrs = &PMAddrSets[F];
	}
	// Collect PM Addresses in functions
		else {
		Optional<DenseSet<Value *>> taintedVals = CFL->taintedVals(*F);
		if (taintedVals) {
			PMAddrSets[F] = *taintedVals;
					PMAddrs = &PMAddrSets[F];
		}
	}

	const Value *Origin = GetUnderlyingObject(Addr, DL);
	for (auto &u : Origin->uses()) {
		if (isa<AllocaInst>(u)) {
			return false;
		}
	}

	if (PMAddrs) {
		if (PMAddrs->find(Addr) != PMAddrs->end()) {
			return true;
		}
	} else
		//assert(false && "PMAddrs not available");

	return false;
}

/** Simple may-analysis for checking if an address is in the heap
 *	TODO: may need more sophisticated checks
 **/
 /*
bool PMRobustness::mayInHeap(const Value * Addr) {
	if (GetElementPtrInst * GEP = dyn_cast<GetElementPtrInst>((Value *)Addr)) {
		Value * BaseAddr = GEP->getPointerOperand();

		for (auto &u : BaseAddr->uses()) {
			if (isa<AllocaInst>(u)) {
				return false;
			}
		}
	} else {
		for (auto &u : Addr->uses()) {
			if (isa<AllocaInst>(u)) {
				return false;
			}
		}
	}

	// TODO: if pointer comes from function parameters; check the caller
	// Attach metadata to each uses of function parameters
	//if (I->getMetadata(FUNC_PARAM_USE)) {}

	// Address may be in the heap. We don't know for sure.
	return true;
}*/

ob_state_t * PMRobustness::getObjectState(state_t *map, const Value *Addr, bool &updated) {
	ob_state_t *object_state = map->lookup(Addr);
	if (object_state == NULL) {
		object_state = new ob_state_t();
		(*map)[Addr] = object_state;
		updated |= true;
	}

	return object_state;
}

ob_state_t * PMRobustness::getObjectState(state_t *map, const Value *Addr) {
	ob_state_t *object_state = map->lookup(Addr);
	if (object_state == NULL) {
		object_state = new ob_state_t();
		(*map)[Addr] = object_state;
	}

	return object_state;
}

void PMRobustness::checkEndError(state_map_t *AbsState, Function &F) {
	SmallPtrSet<Instruction *, 8> &RetSet = FunctionRetInstMap[&F];
	DenseMap<BasicBlock *, addr_set_t> &ArraySets = UnflushedArrays[&F];
	DenseSet<const Value *> &ErrorSet = FunctionEndErrorSets[&F];

	SmallPtrSet<Value *, 8> RetValSet;
	for (Instruction *I : RetSet) {
		Value *Ret = cast<ReturnInst>(I)->getReturnValue();
		RetValSet.insert(Ret);
	}

	for (Instruction *I : RetSet) {
		// 1) Check objects other than parameters/return values that are dirty and escaped
		// Get the state at each return statement
		state_t *state = &(*AbsState)[I];
		bool insertFence = false;
		if (state == NULL)
			continue;

		for (state_t::iterator it = state->begin(); it != state->end(); it++) {
			if (FunctionArguments.find(it->first) != FunctionArguments.end())
				continue;
			else if (RetValSet.find(it->first) != RetValSet.end())
				continue;

			Value *Ret = cast<ReturnInst>(I)->getReturnValue();
			if (Ret == it->first)
				continue;

			ob_state_t *object_state = it->second;
			if (isUnsafeState(object_state)) {
				if (ErrorSet.find(it->first) == ErrorSet.end()) {
					ErrorSet.insert(it->first);

					errs() << "Error!!!!!!! at return statement: ";
					if (isa<Instruction>(it->first) && !isa<PHINode>(it->first)) {
						const Instruction *inst = cast<Instruction>(it->first);

						if (getPosition(inst, true).empty())
							getPosition(I, true);
					} else {
						getPosition(I, true);
					}

					errs() << "@@ Instruction " << *it->first << "\n";
					errs() << object_state->getDirtyEscapedPosStr() << "\n";
					insertFence = true;
				}
			}
		}

		if (insertFence && FlushInsertMode == OPTIMIZED) {
			auto fence = fenceAndChangeState(I, state);
			MDNode *N = MDNode::get(*Ctx, None);
			fence->setMetadata(FUNC_END_FENCE, N);
		}
	}
}

void PMRobustness::checkMultiObjError(state_t *map, Instruction *I, bool non_dirty_escaped_before) {
	SmallVector<const Value *, 4> unsafe_objs;
	bool check_and_report = false;
	IRBuilder<> IRB(I);

	if (!InstructionMarksEscDirObj)
		return;

	// First condition: there are clearly two escaped dirty objects
	for (state_t::iterator it = map->begin(); it != map->end(); it++) {
		ob_state_t *object_state = it->second;
		if (isUnsafeState(object_state)) {
			unsafe_objs.push_back(it->first);

			// There is already one or more escaped dirty objects
			if (unsafe_objs.size() == 2) {
				check_and_report = true;
				break;
			}
		}
	}

	// Second condition: one escaped dirty object and the current instruction is a call
	if (unsafe_objs.size() == 1 && CallMarksEscDirObj) {
		// If unsafe_objs_count was 0 before processCall updated states,
		// then it is not a bug
		// Some of the cases where two fields of an object are dirty are covered here
		if (!non_dirty_escaped_before)
			check_and_report = true;
	}

	if (check_and_report && StmtErrorSet->find(I) == StmtErrorSet->end()) {
		StmtErrorSet->insert(I);
		errs() << "Reporting errors for function: " << I->getFunction()->getName() << "\n";
		errs() << "Error: More than two objects are escaped and dirty/clwb at: ";
		errs() << "@@ Instruction " << *I << "\n";
		errs() << "Dirty/clwb and escaped objects \n";
		for (auto const *Val: unsafe_objs) {
			errs() << "--" << *Val;
			auto it = map->find(Val);
			if (it != map->end())
				errs() << it->second->getDirtyEscapedPosStr();
			errs() <<" \n";
		}
		if (FlushInsertMode == OPTIMIZED) {
				MDNode *N = MDNode::get(*Ctx, None);
			auto fence = fenceAndChangeState(I, map);
			fence->setMetadata(MULTI_OBJ_FENCE, N);
		}
		if (HasTwoUnsafeParams) {
			errs() << "Two Parameters are already escaped dirty, this error may not be real\n";
		}
	}
}

// Report escaped and dirty objects before unlock/atomic release operations on Non PM objects
void PMRobustness::checkReleaseError(state_t *map, Instruction *I) {
	SmallVector<const Value *, 8> unsafe_objs;
	IRBuilder<> IRB(I);

	for (state_t::iterator it = map->begin(); it != map->end(); it++) {
		ob_state_t *object_state = it->second;
		if (isUnsafeState(object_state)) {
			unsafe_objs.push_back(it->first);
		}
	}

	if (unsafe_objs.size() > 0 && StmtErrorSet->find(I) == StmtErrorSet->end()) {
		StmtErrorSet->insert(I);
		errs() << "Reporting NEW1 errors for function: " << I->getFunction()->getName() << "\n";
		errs() << "NEWError: Has escaped and dirty objects before unlock/release atomic operations on non PM objects at: ";
		getPosition(I, true);
		errs() << "@@ Instruction " << *I << "\n";
		errs() << "Dirty and escaped objects \n";
		for(auto *Val: unsafe_objs) {
			errs() << "--" << *Val;
			auto it = map->find(Val);
			if(it != map->end())
			  errs() << " " << it->second->getDirtyEscapedPosStr();
			errs() <<" \n";
		}
		if (FlushInsertMode == OPTIMIZED) {
				MDNode *N = MDNode::get(*Ctx, None);
			auto fence = fenceAndChangeState(I, map);
			fence->setMetadata(RELEASE_OBJ_FENCE, N);
		}
	}
}

void PMRobustness::reportMultipleEscDirtyFieldsError(state_t *map, Instruction *I) {
	IRBuilder<> IRB(I);

	if (StmtErrorSet->find(I) == StmtErrorSet->end()) {
		StmtErrorSet->insert(I);
		errs() << "Reporting NEW2 errors for function: " << I->getFunction()->getName() << "\n";
		errs() << "NEWError2: Has multiple dirty fields on escaped objects at: ";
		getPosition(I, true);
		errs() << "@@ Instruction " << *I << "\n";
		errs() << "previously " << MultiUnsafeFieldsPrevPos << "\n";
		if (FlushInsertMode == OPTIMIZED) {
				MDNode *N = MDNode::get(*Ctx, None);
			auto fence = fenceAndChangeState(I, map);
			fence->setMetadata(MULTI_FIELD_FENCE, N);
		}
	}
}


void PMRobustness::decomposeAddress(DecomposedGEP &DecompGEP, Value *Addr, const DataLayout &DL) {
	unsigned MaxPointerSize = getMaxPointerSize(DL);
	DecompGEP.StructOffset = DecompGEP.OtherOffset = APInt(MaxPointerSize, 0);
	DecompGEP.isArray = false;
	bool GEPMaxLookupReached = DecomposeGEPExpression(Addr, DecompGEP, DL, NULL, NULL);

	if (GEPMaxLookupReached) {
		errs() << "GEP Max Lookup Reached\n";
#ifdef PMROBUST_DEBUG
		assert(false && "GEP Max Lookup Reached; debug\n");
#endif
	}
}

NVMOP PMRobustness::whichNVMoperation(Instruction *I) {
	if (CallInst *callInst = dyn_cast<CallInst>(I)) {
		if (callInst->isInlineAsm()) {
			InlineAsm *asmInline = dyn_cast<InlineAsm>(callInst->getCalledOperand());
			StringRef asmStr = asmInline->getAsmString();
			if (asmStr.contains("mfence") || asmStr.contains("sfence")) {
				//errs() << "mfence/sfence seen at\n";
				//getPosition(I, true);
				//errs() << *I << "\n";
				return NVM_FENCE;
			} else if (asmStr.contains(ASM_CLWB) || asmStr.contains(ASM_CLFLUSHOPT)) {
				return NVM_CLWB;
			} else if (asmStr.contains(ASM_CLFLUSH)) {
				return NVM_CLFLUSH;
			}
		}
	}
	return NVM_UNKNOWN;
}

NVMOP PMRobustness::whichNVMoperation(StringRef flushtype) {
	if (flushtype.contains("mfence") || flushtype.contains("sfence")) {
		return NVM_FENCE;
	} else if (flushtype.contains("clflushopt")) {
		return NVM_CLWB;
	} else if (flushtype.contains("clflush")) {
		return NVM_CLFLUSH;
	}
	return NVM_UNKNOWN;
}

NVMOP PMRobustness::analyzeFlushType(Function &F) {
	NVMOP op = NVM_UNKNOWN;
	if (F.hasFnAttribute("flush_type")) {
		StringRef flushtype = F.getFnAttribute("flush_type").getValueAsString();
		return whichNVMoperation(flushtype);
	}

	for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
		if (isFlushWrapperFunction(&*I)) {
			CallBase *callInst = cast<CallBase>(&*I);
			Function *callee = callInst->getCalledFunction();
			op = analyzeFlushType(*callee);
		} else {
			op = whichNVMoperation(&*I);
		}
		if (op == NVM_CLWB) {
			F.addFnAttr("flush_type", "clflushopt");
			break;
		} else if (op == NVM_CLFLUSH) {
			F.addFnAttr("flush_type", "clflush");
			break;
		} else if (op == NVM_FENCE) {
			continue;
		}
	}

	return op;
}

bool PMRobustness::isInFunctionAnnotation(Instruction *I) {
	if (CallBase *CB = dyn_cast<CallBase>(I)) {
		if (Function *callee = CB->getCalledFunction()) {
			if (callee->getName() == "pm_ignore_block_begin" ||
				callee->getName() == "pm_ignore_block_end") {
				return true;
			}
		}
	}

	return false;
}

bool PMRobustness::isFunctionAnnotated(Instruction *I) {
	if (CallBase *CB = dyn_cast<CallBase>(I)) {
		if (Function *callee = CB->getCalledFunction()) {
			for (StringRef &s : AnnotationList) {
				if (callee->hasFnAttribute(s))
					return true;
			}
		}
	}

	return false;
}

bool PMRobustness::isFunctionAnnotated(Function &F) {
	for (StringRef &s : AnnotationList) {
		if (F.hasFnAttribute(s))
			return true;
	}

	return false;
}

bool PMRobustness::isFlushWrapperFunction(Instruction *I) {
	if (CallBase *CB = dyn_cast<CallBase>(I)) {
		if (Function *callee = CB->getCalledFunction()) {
			if (callee->hasFnAttribute("myflush"))
				return true;
		}
	}

	return false;
}

bool PMRobustness::isMutexLock(Instruction *I) {
	if (CallBase *CB = dyn_cast<CallBase>(I)) {
		if (Function *callee = CB->getCalledFunction()) {
			if (callee->getName() == "pthread_mutex_lock")
				return true;
		}
	}

	return false;
}

bool PMRobustness::isMutexUnlock(Instruction *I) {
	if (CallBase *CB = dyn_cast<CallBase>(I)) {
		if (Function *callee = CB->getCalledFunction()) {
			if (callee->getName() == "pthread_mutex_unlock")
				return true;
		}
	}

	return false;
}

inline addr_set_t * PMRobustness::getUnflushedAddrSet(Function *F, BasicBlock *B) {
	return &UnflushedArrays[F][B];
}

bool PMRobustness::checkUnflushedAddress(Function *F, addr_set_t * AddrSet, Value * Addr, NVMOP op) {
	addr_set_t::iterator it = AddrSet->find(Addr);
	if (it == AddrSet->end()) {
		errs() << "flush an array address not seen before" << *Addr << "\n";
		return false;
	}

	if (op == NVM_CLFLUSH) {
		AddrSet->erase(it);
	} else if (op == NVM_CLWB) {
		ParamStateType s = it->second.getState();
		if (s == ParamStateType::DIRTY_ESCAPED) {
			it->second.setState(ParamStateType::CLWB_ESCAPED);
		}

		assert(s != ParamStateType::DIRTY_CAPTURED);
	}

	//errs() << "Addr is flushed: " << *Addr << "\n";
	return true;
}

bool PMRobustness::checkPointerArithmetics(Value *Addr, const DataLayout &DL) {
	const Value *Origin = GetUnderlyingObject(Addr, DL);
	if (isa<IntToPtrInst>(Origin)) {
		return true;
	}

	return false;
}

bool PMRobustness::compareDecomposedGEP(DecomposedGEP &GEP1, DecomposedGEP &GEP2) {
	if (GEP1.OtherOffset != GEP2.OtherOffset ||
		GEP1.StructOffset != GEP2.StructOffset) {
		return false;
	}

	if (GEP1.VarIndices.size() != GEP2.VarIndices.size())
		return false;

	for (unsigned i = 0; i < GEP1.VarIndices.size(); i++) {
		if (GEP1.VarIndices[i] != GEP2.VarIndices[i]) {
			return false;
		}
	}

	return true;
}

CallingContext * PMRobustness::computeContext(state_t *map, Instruction *I) {
	CallBase *CB = cast<CallBase>(I);
	const DataLayout &DL = I->getModule()->getDataLayout();
	//if (CB->arg_size() == 0)
	//	return NULL;

	CallingContext *context = new CallingContext();

	//Function *F = CB->getCalledFunction();
	//F->dump();

	unsigned i = 0;
	for (User::op_iterator it = CB->arg_begin(); it != CB->arg_end(); it++) {
		Value *op = *it;

		if (op->getType()->isPointerTy() && isPMAddr(I->getFunction(), op, DL)) {
			DecomposedGEP DecompGEP;
			decomposeAddress(DecompGEP, op, DL);
			unsigned offset = DecompGEP.getOffsets();

			if (DecompGEP.isArray || offset == UNKNOWNOFFSET || offset == VARIABLEOFFSET) {
				// TODO: We have information about arrays escaping or not.
				// Dirty array slots are stored in UnflushedArrays

				// FIXME
				context->addAbsInput(ParamStateType::TOP);
			} else {
				ob_state_t *object_state = map->lookup(DecompGEP.Base);
				ParamStateType absState = ParamStateType::TOP;
				if (object_state != NULL) {
					unsigned TypeSize = getFieldSize(op, DL);
					//errs() << "Base: " << *DecompGEP.Base << " of instruction " << *I <<"\n";
					//errs() << "offset: " << offset << "; field size: " << TypeSize << "\n";
					//errs() << "checking state of op: " << *op << "\n";

					if (object_state->getSize() == 0 && FunctionArguments.find(op) != FunctionArguments.end()) {
						// The parent function's parameter is passed to call site without any modification
						absState = CurrentContext->getStateType(FunctionArguments.lookup(op));
					} else {
						absState = object_state->checkState(offset, TypeSize);
					}
				}

				context->addAbsInput(absState);
			}
		} else {
			context->addAbsInput(ParamStateType::NON_PMEM);
		}

		i++;
	}

	return context;
}

void PMRobustness::lookupFunctionResult(state_t *map, CallBase *CB, CallingContext *Context,
	bool &non_dirty_escaped_before, bool &report_release_error) {
	Function *F = CB->getCalledFunction();
	FunctionSummary *FS = getOrCreateFunctionSummary(F);
	const DataLayout &DL = CB->getModule()->getDataLayout();
	bool use_higher_results = false;

	// Set has_release bit for caller
	if (FS->hasRelease()) {
		FunctionSummary *parentFS = getOrCreateFunctionSummary(CB->getFunction());
		parentFS->setRelease();
		//errs() << "Set Release Instruction: " << *CB << "\n";
		//errs() << "For " << CB->getFunction()->getName() << "\n";

		report_release_error = true;
	}

	if (FS->isFenced()) {
		processFence(map, CB);
	}

#ifdef DUMP_CACHED_RESULT
	errs() << "lookup results for function: " << F->getName() << " with Context:\n";
	Context->dump();
#endif

	OutputState *out_state = FS->getResult(Context);
	// Function has not been analyzed with the context
	// TODO: If there are multiple contexts higher than the current context, use merged results
	if (out_state == NULL) {
		if (UniqueFunctionSet.find(std::make_pair(F, Context)) == UniqueFunctionSet.end()) {
			FunctionWorklist.emplace_back(F, Context);
			UniqueFunctionSet.insert(std::make_pair(F, Context));
			//errs() << "(LOG6) Function " << F->getName() << " added to worklist in " << CB->getFunction()->getName() << "\n";
		} else {
			delete Context;
		}

		out_state = FS->getLeastUpperResult(Context);
		if (out_state == NULL) {
			// No least upper context exists
			// Mark all parameters as TOP (clean and captured)
			makeParametersTOP(map, CB);
#ifdef DUMP_CACHED_RESULT
			errs() << "Function cached result not found. Make all parameters TOP\n\n";
#endif
			return;
		} else {
			use_higher_results = true;
		}
	}

#ifdef DUMP_CACHED_RESULT
	errs() << "Function cached result found\n";
	if (use_higher_results)
		errs() << "Higher contexts are used\n";
	out_state->dump();
#endif

	// For reporting in-function error
	if (out_state->marksEscDirObj) {
		InstructionMarksEscDirObj = true;
		FunctionMarksEscDirObj = true;
	}

	if (!use_higher_results && out_state->marksEscDirObjConditional) {
		CallMarksEscDirObj = true;
	}

	if (CallMarksEscDirObj) {
		for (state_t::iterator it = map->begin(); it != map->end(); it++) {
			ob_state_t *object_state = it->second;
			if (object_state->isEscaped() && object_state->isDirty()) {
				non_dirty_escaped_before = false;
				break;
			}
		}

	}

	// Use cached result to modify parameter states
	unsigned i = 0;
	for (User::op_iterator it = CB->arg_begin(); it != CB->arg_end(); it++) {
		Value *op = *it;
		
		if (Context->getStateType(i) == ParamStateType::NON_PMEM) {
			// Ignore NON_PMEM input parameters
			assert(out_state->getStateType(i) == ParamStateType::NON_PMEM);
			i++;
			continue;
		} else if (out_state->getStateType(i) == ParamStateType::NON_PMEM) {
			// It has happened that when the input is top, the output is NON_PMEM
			i++;
			continue;
		}

		DecomposedGEP DecompGEP;
		decomposeAddress(DecompGEP, op, DL);
		unsigned offset = DecompGEP.getOffsets();

		if (DecompGEP.isArray || offset == UNKNOWNOFFSET || offset == VARIABLEOFFSET) {
			ob_state_t *object_state = getObjectState(map, DecompGEP.Base);
			object_state->setToArray();
		}
		unsigned TypeSize = getFieldSize(op, DL);
		if (TypeSize == (unsigned)-1) {
			i++;
			continue;
		}

		ob_state_t *object_state = getObjectState(map, DecompGEP.Base);
		ParamStateType param_state = out_state->getStateType(i);
		if (param_state == ParamStateType::DIRTY_CAPTURED) {
			// Approximate dirty
			if (Context->getState(i).isClean()) {
				// Note: We don't recapture escaped objects
				// If input state is clean, then use DirtyBytesInfo to get dirty bytes
				DirtyBytesInfo *info = out_state->getDirtyBytesInfo(i);
				std::vector<std::pair<int, int>> *lst = info->getDirtyBytes();

				//assert(offset != UNKNOWNOFFSET && offset != VARIABLEOFFSET);
				for (unsigned i = 0; i < lst->size(); i++) {
					std::pair<int, int> &elem = (*lst)[i];
					object_state->setDirty(offset + elem.first, elem.second - elem.first, CB);
				}
			} else if (!out_state->isUntouched(i)) {
				object_state->setDirty(offset, TypeSize, CB);
			}
		} else if (param_state == ParamStateType::DIRTY_ESCAPED) {
			// Approximate dirty
			if (Context->getState(i).isClean()) {
				// Note: We don't recapture escaped objects
				// If input state is clean, then use DirtyBytesInfo to get dirty bytes
				DirtyBytesInfo *info = out_state->getDirtyBytesInfo(i);
				std::vector<std::pair<int, int>> *lst = info->getDirtyBytes();

				//assert(offset != UNKNOWNOFFSET && offset != VARIABLEOFFSET);
				for (unsigned i = 0; i < lst->size(); i++) {
					std::pair<int, int> &elem = (*lst)[i];
					object_state->setDirty(offset + elem.first, elem.second - elem.first, CB);
				}
			} else if (!out_state->isUntouched(i)) {
				object_state->setDirty(offset, TypeSize, CB);
			}

			object_state->setEscape(CB);
		} else if (param_state == ParamStateType::CLWB_CAPTURED) {
			object_state->setClwb(offset, TypeSize);
		} else if (param_state == ParamStateType::CLWB_ESCAPED) {
			object_state->setClwb(offset, TypeSize);
			object_state->setEscape(CB);
		} else if (param_state == ParamStateType::CLEAN_CAPTURED) {
			object_state->setFlush(offset, TypeSize);
		} else if (param_state == ParamStateType::CLEAN_ESCAPED) {
			object_state->setFlush(offset, TypeSize);
			object_state->setEscape(CB);
		} else if (param_state == ParamStateType::TOP) {
			object_state->setFlush(offset, TypeSize);
			object_state->setCaptured();
		} else {
			assert(false && "other cases");
		}
		

		i++;
	}

	if (out_state->hasRetVal) {
		modifyReturnState(map, CB, out_state);
	}
}

// Get initial states of parameters from Context
void PMRobustness::computeInitialState(state_t *map, Function &F, CallingContext *Context) {
	assert(F.arg_size() == Context->AbstractInputState.size());
	const DataLayout &DL = F.getParent()->getDataLayout();

	for (state_t::iterator it = map->begin(); it != map->end(); it++)
		delete it->second;

	map->clear();

	unsigned i = 0;
	for (Function::arg_iterator it = F.arg_begin(); it != F.arg_end(); it++) {
		ParamStateType PS = Context->getStateType(i);
		i++;

		Argument *Arg = &*it;
		ob_state_t *object_state = getObjectState(map, Arg);

		if (PS == ParamStateType::NON_PMEM) {
			object_state->setNonPmem();
			continue;
		}

		unsigned TypeSize = getFieldSize(Arg, DL);
		if (TypeSize == (unsigned)-1) {
			continue;
		}
		//TODO: save position in ParamState to have precise position information here
		Instruction *first_inst = (F.begin() != F.end() && F.begin()->begin() != F.begin()->end())? 
									&*F.begin()->begin():
									nullptr;

		if (PS == ParamStateType::DIRTY_CAPTURED) {
			// TODO: how to better approximate dirty
			object_state->setDirty(0, TypeSize, first_inst);
		} else if (PS == ParamStateType::DIRTY_ESCAPED) {
			// TODO: how to better approximate dirty
			object_state->setDirty(0, TypeSize, first_inst);
			object_state->setEscape(first_inst);
		} else if (PS == ParamStateType::CLWB_CAPTURED) {
			object_state->setClwb(0, TypeSize);
		} else if (PS == ParamStateType::CLWB_ESCAPED) {
			object_state->setClwb(0, TypeSize);
			object_state->setEscape(first_inst);
		} else if (PS == ParamStateType::CLEAN_CAPTURED) {
			object_state->setFlush(0, TypeSize);
		} else if (PS == ParamStateType::CLEAN_ESCAPED) {
			object_state->setFlush(0, TypeSize);
			object_state->setEscape(first_inst);
		} else if (PS == ParamStateType::TOP) {
			// TOP: clean and captured
			object_state->setFlush(0, TypeSize);
		} else {
			// BOTTOM, etc.
			// Not sure what to do
		}
	}
}

// Get final states of parameters and return value from Function F
bool PMRobustness::computeFinalState(state_map_t *AbsState, Function &F, CallingContext *Context) {
	const DataLayout &DL = F.getParent()->getDataLayout();
	SmallPtrSet<Instruction *, 8> &RetSet = FunctionRetInstMap[&F];
	DenseMap<const BasicBlock *, bool> &fence_analysis = FenceAnalysisMap[&F];

	FunctionSummary *FS = getOrCreateFunctionSummary(&F);
	OutputState *Output = FS->getOrCreateResult(Context);

	bool is_fenced = true;
	state_t final_state;
	for (Instruction *I : RetSet) {
		// check fense state at each return statement
		is_fenced &= fence_analysis[I->getParent()];

		// Get the state at each return statement
		auto itr = AbsState->find(I);
		if (itr == AbsState->end()) {
			continue;
		}
			state_t *s = &itr->second;

		// Merge the state of each function paremeter. This is a conservative approximation.
		for (Function::arg_iterator it = F.arg_begin(); it != F.arg_end(); it++) {
			Argument *Arg = &*it;
			ob_state_t *A = final_state.lookup(Arg);
			ob_state_t *B = s->lookup(Arg);

			if (B == NULL)
				continue;

			if (A == NULL)
				final_state[Arg] = new ob_state_t(B);
			else {
				A->mergeFrom(B);
			}
		}
	}

	if (is_fenced) {
		// set flag if all path to exits has a memory fence
		FS->setFenced();
	}

	bool updated = false;
	updated |= FS->justSetRelease();

	unsigned i = 0;
	Output->AbstractOutputState.resize(F.arg_size());
	for (Function::arg_iterator it = F.arg_begin(); it != F.arg_end(); it++) {
		Argument *Arg = &*it;

		ob_state_t *object_state = final_state.lookup(Arg);
		if (object_state == NULL || object_state->isNonPmem()) {
			if (Output->getStateType(i) != ParamStateType::NON_PMEM) {
				Output->AbstractOutputState[i].setState(ParamStateType::NON_PMEM);
				updated = true;
			}

			i++;
			continue;
		}

		ParamStateType absState;
		if (object_state->getSize() == 0) {
			// No store to the parameter; TODO: how about loads?
			absState = Context->getStateType(i);
		} else {
			unsigned TypeSize = getFieldSize(Arg, DL);
			absState = object_state->checkState(0, TypeSize);

			// If the input state is clean, add dirty btyes to list
			ParamState &input_state = Context->getState(i);
			if (input_state.isClean()) {
				if (absState == ParamStateType::DIRTY_CAPTURED || absState == ParamStateType::DIRTY_ESCAPED) {
					DirtyBytesInfo *info = Output->getOrCreateDirtyBytesInfo(i);
					object_state->computeDirtyBytes(*info);
				} // TODO: else if (CLWB_CAPTURED/CLWB_ESCAPED)
			}
		}

		if (Output->getStateType(i) != absState) {
			Output->AbstractOutputState[i].setState(absState);
			updated = true;
		}

		i++;
	}

	// Cache return Type
	Type *RetType = F.getReturnType();
	if (RetType->isVoidTy()) {
		Output->hasRetVal = false;
	} else if (RetType->isPointerTy()) {
		Output->hasRetVal = true;
		//Output->retVal = object_state->checkState();
		ParamState PS(ParamStateType::TOP);
		for (Instruction *I : RetSet) {
					auto itr = AbsState->find(I);
			if (itr == AbsState->end()) {
				continue;
				}
					state_t *s = &itr->second;

			Value *Ret = cast<ReturnInst>(I)->getReturnValue();
			ob_state_t *RetState = s->lookup(Ret);

			if (RetState != NULL) {
				ParamStateType tmp_state = RetState->checkState();
				ParamState tmp = ParamState(tmp_state);
				if (tmp.isLowerThan(PS)) {
					//errs() << tmp.print() << " < " << PS.print() << "\n";
					PS.setState(tmp_state);
				}
			}
		}

		if (Output->retVal.get_state() != PS.get_state()) {
			Output->retVal.setState(PS.get_state());
			updated = true;
		}
	} else {
		//errs() << "RetVal non PMEM\n";
		Output->hasRetVal = true;

		if (Output->retVal.get_state() != ParamStateType::NON_PMEM) {
			Output->retVal.setState(ParamStateType::NON_PMEM);
			updated = true;
		}
	}

	if (FunctionMarksEscDirObj) {
		Output->marksEscDirObj = true;

		// all parameters are not dirty escaped
		bool non_dirty_escaped = true;
		for (unsigned i = 0; i < Context->AbstractInputState.size(); i++) {
			ParamState &state = Context->getState(i);
			if (state.isDirtyEscaped()) {
				non_dirty_escaped = false;
				break;
			}
		}

		if (non_dirty_escaped) {
			Output->marksEscDirObjConditional = true;
		}
	}

	if (!Output->checkUntouched) {
		unsigned i = 0;
		for (Function::arg_iterator it = F.arg_begin(); it != F.arg_end(); it++) {
			Argument *Arg = &*it;
			if (Arg->getNumUses() == 0)
				Output->setUntouched(i);

			i++;
		}
	}

	// Free memory in temporarily allocated final_state object
	for (state_t::iterator it = final_state.begin(); it != final_state.end(); it++) {
		delete it->second;
	}

	checkEndError(AbsState, F);

	return updated;
}

FunctionSummary * PMRobustness::getOrCreateFunctionSummary(Function *F) {
	return &FunctionSummaries[F];
}

// Mark all parameters as TOP (clean and captured)
void PMRobustness::makeParametersTOP(state_t *map, CallBase *CB) {
	const DataLayout &DL = CB->getModule()->getDataLayout();
	for (User::op_iterator it = CB->arg_begin(); it != CB->arg_end(); it++) {
		Value *op = *it;

		if (op->getType()->isPointerTy() && isPMAddr(CB->getFunction(), op, DL)) {
			DecomposedGEP DecompGEP;
			decomposeAddress(DecompGEP, op, DL);
			unsigned offset = DecompGEP.getOffsets();

			if (DecompGEP.isArray || offset == UNKNOWNOFFSET || offset == VARIABLEOFFSET) {
				// TODO: What do we do here?
				ob_state_t *object_state = getObjectState(map, DecompGEP.Base);
				object_state->setToArray();
			}
			ob_state_t *object_state = getObjectState(map, DecompGEP.Base);
			unsigned TypeSize = getFieldSize(op, DL);
			//errs() << "TypeSize: " << TypeSize << "\n";
			//errs() << *op << "\n";

			if (TypeSize == (unsigned)-1)
				object_state->setFlush(offset, TypeSize, true);
			else
				object_state->setFlush(offset, TypeSize);

			object_state->setCaptured();
		} // Else case: op is NON_PMEM, so don't do anything
	}
}

void PMRobustness::modifyReturnState(state_t *map, CallBase *CB, OutputState *out_state) {
	const DataLayout &DL = CB->getModule()->getDataLayout();
	ParamStateType return_state = out_state->retVal.get_state();
	if (return_state == ParamStateType::NON_PMEM)
		return;

	DecomposedGEP DecompGEP;
	decomposeAddress(DecompGEP, CB, DL);
	unsigned offset = DecompGEP.getOffsets();

	if (DecompGEP.isArray || offset == UNKNOWNOFFSET || offset == VARIABLEOFFSET) {
		//Weiyu, Why?
		assert(false);
	} else {
		unsigned TypeSize = getFieldSize(CB, DL);
		if (TypeSize == (unsigned)-1) {
			errs() << "CB " << *CB << " has field size -1; so it is a function type\n";
			//errs() << *CB->getFunction() << "\n";
			//assert(false);
			return;
		}

		ob_state_t *object_state = getObjectState(map, DecompGEP.Base);

		if (return_state == ParamStateType::DIRTY_CAPTURED) {
			// Approximate dirty
			object_state->setDirty(offset, TypeSize, CB);
		} else if (return_state == ParamStateType::DIRTY_ESCAPED) {
			// TODO: How to approximate dirty?
			//assert(false);
			object_state->setEscape(CB);
			object_state->setDirty(offset, TypeSize, CB);
		} else if (return_state == ParamStateType::CLWB_CAPTURED) {
			object_state->setClwb(offset, TypeSize);
		} else if (return_state == ParamStateType::CLWB_ESCAPED) {
			object_state->setClwb(offset, TypeSize);
			object_state->setEscape(CB);
		} else if (return_state == ParamStateType::CLEAN_CAPTURED) {
			object_state->setFlush(offset, TypeSize);
		} else if (return_state == ParamStateType::CLEAN_ESCAPED) {
			object_state->setFlush(offset, TypeSize);
			object_state->setEscape(CB);
		} else if (return_state == ParamStateType::TOP) {
			object_state->setFlush(offset, TypeSize);
			object_state->setCaptured();
		} else {
			assert(false && "other cases");
		}
	}
}

alias_set_t * PMRobustness::getFunctionAliasSet(Function *F) {
	alias_set_t *AliasSet = FunctionAliasSet.lookup(F);
	if (AliasSet == NULL) {
		AliasSet = new alias_set_t();
		FunctionAliasSet[F] = AliasSet;
	}

	return AliasSet;
}

value_set_t * PMRobustness::getValueAliasSet(Function *F, Value *V) {
	alias_set_t *AliasSet = FunctionAliasSet.lookup(F);
	if (AliasSet == NULL)
		return NULL;

	value_set_t *set = AliasSet->lookup(V);
	return set;
}

void PMRobustness::computeAliasSet(PHINode *PHI) {
	alias_set_t *AliasSet = getFunctionAliasSet(PHI->getFunction());
	Value *V1 = PHI;
	// TODO: use GetUnderlyingObject
	for (unsigned i = 0; i != PHI->getNumIncomingValues(); i++) {
		Value *V2 = PHI->getIncomingValue(i);
		if (isa<ConstantPointerNull>(V1)) {
			V1 = V2;
			continue;
		} else if (isa<ConstantPointerNull>(V2)) {
			continue;
		}

		value_set_t *set1 = AliasSet->lookup(V1);
		value_set_t *set2 = AliasSet->lookup(V2);
		if (set1 == NULL && set1 == NULL) {
			// create value_set_t and add both values
			set1 = new value_set_t();
			set1->insert(V1);
			set1->insert(V2);
			(*AliasSet)[V1] = set1;
			(*AliasSet)[V2] = set1;
		} else if (set1 == NULL) {
			// set2 is not NULL; add V1 to the set of set2
			set2->insert(V1);
			(*AliasSet)[V1] = set2;
		} else if (set2 == NULL){
			// set1 is not NULL; add V1 to the set of V2
			set1->insert(V2);
			(*AliasSet)[V2] = set1;
		} else if (set1 == set2) {
			// Do nothing
		} else {
			// merge set1 and set2; remove set1
			set1->insert(set2->begin(), set2->end());
			// Update the reference for each member in set2
			for (Value *u : *set2) {
				(*AliasSet)[u] = set1;
			}

			delete set2;
		}

		V1 = V2;
	}
}

//===----------------------------------------------------------------------===//
// GetElementPtr Instruction Decomposition and Analysis
//===----------------------------------------------------------------------===//
/// Copied from Analysis/BasicAliasAnalysis.cpp
/// Analyzes the specified value as a linear expression: "A*V + B", where A and
/// B are constant integers.
///
/// Returns the scale and offset values as APInts and return V as a Value*, and
/// return whether we looked through any sign or zero extends.	The incoming
/// Value is known to have IntegerType, and it may already be sign or zero
/// extended.
///
/// Note that this looks through extends, so the high bits may not be
/// represented in the result.
const Value *PMRobustness::GetLinearExpression(
	const Value *V, APInt &Scale, APInt &Offset, unsigned &ZExtBits,
	unsigned &SExtBits, const DataLayout &DL, unsigned Depth,
	AssumptionCache *AC, DominatorTree *DT, bool &NSW, bool &NUW) {

	assert(V->getType()->isIntegerTy() && "Not an integer value");
	// Limit our recursion depth.
	if (Depth == 6) {
		Scale = 1;
		Offset = 0;
		return V;
	}

	if (const ConstantInt *Const = dyn_cast<ConstantInt>(V)) {
		// If it's a constant, just convert it to an offset and remove the variable.
		// If we've been called recursively, the Offset bit width will be greater
		// than the constant's (the Offset's always as wide as the outermost call),
		// so we'll zext here and process any extension in the isa<SExtInst> &
		// isa<ZExtInst> cases below.
		Offset += Const->getValue().zextOrSelf(Offset.getBitWidth());
		assert(Scale == 0 && "Constant values don't have a scale");
		return V;
	}

	if (const BinaryOperator *BOp = dyn_cast<BinaryOperator>(V)) {
		if (ConstantInt *RHSC = dyn_cast<ConstantInt>(BOp->getOperand(1))) {
			// If we've been called recursively, then Offset and Scale will be wider
			// than the BOp operands. We'll always zext it here as we'll process sign
			// extensions below (see the isa<SExtInst> / isa<ZExtInst> cases).
			APInt RHS = RHSC->getValue().zextOrSelf(Offset.getBitWidth());

			switch (BOp->getOpcode()) {
			default:
				// We don't understand this instruction, so we can't decompose it any
				// further.
				Scale = 1;
				Offset = 0;
				return V;
			case Instruction::Or:
				// X|C == X+C if all the bits in C are unset in X.	Otherwise we can't
				// analyze it.
				if (!MaskedValueIsZero(BOp->getOperand(0), RHSC->getValue(), DL, 0, AC,
						 BOp, DT)) {
					Scale = 1;
					Offset = 0;
					return V;
				}
				LLVM_FALLTHROUGH;
			case Instruction::Add:
				V = GetLinearExpression(BOp->getOperand(0), Scale, Offset, ZExtBits,
						SExtBits, DL, Depth + 1, AC, DT, NSW, NUW);
				Offset += RHS;
				break;
			case Instruction::Sub:
				V = GetLinearExpression(BOp->getOperand(0), Scale, Offset, ZExtBits,
						SExtBits, DL, Depth + 1, AC, DT, NSW, NUW);
				Offset -= RHS;
				break;
			case Instruction::Mul:
				V = GetLinearExpression(BOp->getOperand(0), Scale, Offset, ZExtBits,
						SExtBits, DL, Depth + 1, AC, DT, NSW, NUW);
				Offset *= RHS;
				Scale *= RHS;
				break;
			case Instruction::Shl:
				V = GetLinearExpression(BOp->getOperand(0), Scale, Offset, ZExtBits,
						SExtBits, DL, Depth + 1, AC, DT, NSW, NUW);

				// We're trying to linearize an expression of the kind:
				//	 shl i8 -128, 36
				// where the shift count exceeds the bitwidth of the type.
				// We can't decompose this further (the expression would return
				// a poison value).
				if (Offset.getBitWidth() < RHS.getLimitedValue() ||
						Scale.getBitWidth() < RHS.getLimitedValue()) {
					Scale = 1;
					Offset = 0;
					return V;
				}

				Offset <<= RHS.getLimitedValue();
				Scale <<= RHS.getLimitedValue();
				// the semantics of nsw and nuw for left shifts don't match those of
				// multiplications, so we won't propagate them.
				NSW = NUW = false;
				return V;
			}

			if (isa<OverflowingBinaryOperator>(BOp)) {
				NUW &= BOp->hasNoUnsignedWrap();
				NSW &= BOp->hasNoSignedWrap();
			}
			return V;
		}
	}

	// Since GEP indices are sign extended anyway, we don't care about the high
	// bits of a sign or zero extended value - just scales and offsets.	The
	// extensions have to be consistent though.
	if (isa<SExtInst>(V) || isa<ZExtInst>(V)) {
		Value *CastOp = cast<CastInst>(V)->getOperand(0);
		unsigned NewWidth = V->getType()->getPrimitiveSizeInBits();
		unsigned SmallWidth = CastOp->getType()->getPrimitiveSizeInBits();
		unsigned OldZExtBits = ZExtBits, OldSExtBits = SExtBits;
		const Value *Result =
				GetLinearExpression(CastOp, Scale, Offset, ZExtBits, SExtBits, DL,
					Depth + 1, AC, DT, NSW, NUW);

		// zext(zext(%x)) == zext(%x), and similarly for sext; we'll handle this
		// by just incrementing the number of bits we've extended by.
		unsigned ExtendedBy = NewWidth - SmallWidth;

		if (isa<SExtInst>(V) && ZExtBits == 0) {
			// sext(sext(%x, a), b) == sext(%x, a + b)

			if (NSW) {
				// We haven't sign-wrapped, so it's valid to decompose sext(%x + c)
				// into sext(%x) + sext(c). We'll sext the Offset ourselves:
				unsigned OldWidth = Offset.getBitWidth();
				Offset = Offset.trunc(SmallWidth).sext(NewWidth).zextOrSelf(OldWidth);
			} else {
				// We may have signed-wrapped, so don't decompose sext(%x + c) into
				// sext(%x) + sext(c)
				Scale = 1;
				Offset = 0;
				Result = CastOp;
				ZExtBits = OldZExtBits;
				SExtBits = OldSExtBits;
			}
			SExtBits += ExtendedBy;
		} else {
			// sext(zext(%x, a), b) = zext(zext(%x, a), b) = zext(%x, a + b)

			if (!NUW) {
				// We may have unsigned-wrapped, so don't decompose zext(%x + c) into
				// zext(%x) + zext(c)
				Scale = 1;
				Offset = 0;
				Result = CastOp;
				ZExtBits = OldZExtBits;
				SExtBits = OldSExtBits;
			}
			ZExtBits += ExtendedBy;
		}

		return Result;
	}

	Scale = 1;
	Offset = 0;
	return V;
}

/// If V is a symbolic pointer expression, decompose it into a base pointer
/// with a constant offset and a number of scaled symbolic offsets.
///
/// The scaled symbolic offsets (represented by pairs of a Value* and a scale
/// in the VarIndices vector) are Value*'s that are known to be scaled by the
/// specified amount, but which may have other unrepresented high bits. As
/// such, the gep cannot necessarily be reconstructed from its decomposed form.
///
/// When DataLayout is around, this function is capable of analyzing everything
/// that GetUnderlyingObject can look through. To be able to do that
/// GetUnderlyingObject and DecomposeGEPExpression must use the same search
/// depth (MaxLookupSearchDepth). When DataLayout not is around, it just looks
/// through pointer casts.
bool PMRobustness::DecomposeGEPExpression(const Value *V,
		DecomposedGEP &Decomposed, const DataLayout &DL, AssumptionCache *AC,
		DominatorTree *DT) {
	// Limit recursion depth to limit compile time in crazy cases.
	unsigned MaxLookup = MaxLookupSearchDepth;
	//SearchTimes++;

	unsigned MaxPointerSize = getMaxPointerSize(DL);
	Decomposed.VarIndices.clear();
	do {
		// See if this is a bitcast or GEP.
		const Operator *Op = dyn_cast<Operator>(V);
		if (!Op) {
			// The only non-operator case we can handle are GlobalAliases.
			if (const GlobalAlias *GA = dyn_cast<GlobalAlias>(V)) {
				if (!GA->isInterposable()) {
					V = GA->getAliasee();
					continue;
				}
			}
			Decomposed.Base = V;
			return false;
		}

		if (Op->getOpcode() == Instruction::BitCast ||
				Op->getOpcode() == Instruction::AddrSpaceCast) {
			V = Op->getOperand(0);
			continue;
		}

		const GEPOperator *GEPOp = dyn_cast<GEPOperator>(Op);
		if (!GEPOp) {
			if (const auto *Call = dyn_cast<CallBase>(V)) {
				// CaptureTracking can know about special capturing properties of some
				// intrinsics like launder.invariant.group, that can't be expressed with
				// the attributes, but have properties like returning aliasing pointer.
				// Because some analysis may assume that nocaptured pointer is not
				// returned from some special intrinsic (because function would have to
				// be marked with returns attribute), it is crucial to use this function
				// because it should be in sync with CaptureTracking. Not using it may
				// cause weird miscompilations where 2 aliasing pointers are assumed to
				// noalias.
				if (auto *RP = getArgumentAliasingToReturnedPointer(Call)) {
					V = RP;
					continue;
				}
			}

			// If it's not a GEP, hand it off to SimplifyInstruction to see if it
			// can come up with something. This matches what GetUnderlyingObject does.
			if (const Instruction *I = dyn_cast<Instruction>(V))
				// TODO: Get a DominatorTree and AssumptionCache and use them here
				// (these are both now available in this function, but this should be
				// updated when GetUnderlyingObject is updated). TLI should be
				// provided also.
				if (const Value *Simplified =
								SimplifyInstruction(const_cast<Instruction *>(I), DL)) {
					V = Simplified;
					continue;
				}

			Decomposed.Base = V;
			return false;
		}

		// Don't attempt to analyze GEPs over unsized objects.
		if (!GEPOp->getSourceElementType()->isSized()) {
			Decomposed.Base = V;
			return false;
		}
		unsigned AS = GEPOp->getPointerAddressSpace();
		// Walk the indices of the GEP, accumulating them into BaseOff/VarIndices.
		gep_type_iterator GTI = gep_type_begin(GEPOp);
		unsigned PointerSize = DL.getPointerSizeInBits(AS);
		// Assume all GEP operands are constants until proven otherwise.
		bool GepHasConstantOffset = true;

		//WTF: this treats all struct GEPs and arrays, Weiyu!!
		// Detecing array
		//const Value * firstIndex = *(GEPOp->op_begin() + 1);
		//if (const ConstantInt *CIdx = dyn_cast<ConstantInt>(firstIndex)) {
		//	unsigned FieldNo = CIdx->getZExtValue();
		//	if (FieldNo != 0 || dyn_cast<ArrayType>(GEPOp->getSourceElementType())) {
		//		Decomposed.isArray = true;
		//		//return false;
		//	}
		//}

		for (User::const_op_iterator I = GEPOp->op_begin() + 1, E = GEPOp->op_end();
				 I != E; ++I, ++GTI) {
			const Value *Index = *I;
			// Compute the (potentially symbolic) offset in bytes for this index.
			if (StructType *STy = GTI.getStructTypeOrNull()) {
				// For a struct, add the member offset.
				unsigned FieldNo = cast<ConstantInt>(Index)->getZExtValue();
				if (FieldNo == 0)
					continue;

				Decomposed.StructOffset +=
					DL.getStructLayout(STy)->getElementOffset(FieldNo);

				continue;
			}

			// For an array/pointer, add the element offset, explicitly scaled.
			if (const ConstantInt *CIdx = dyn_cast<ConstantInt>(Index)) {
				if (CIdx->isZero())
					continue;
				Decomposed.OtherOffset +=
					(DL.getTypeAllocSize(GTI.getIndexedType()) *
						CIdx->getValue().sextOrSelf(MaxPointerSize))
						.sextOrTrunc(MaxPointerSize);
				continue;
			}

			GepHasConstantOffset = false;

			APInt Scale(MaxPointerSize, DL.getTypeAllocSize(GTI.getIndexedType()));
			unsigned ZExtBits = 0, SExtBits = 0;

			// If the integer type is smaller than the pointer size, it is implicitly
			// sign extended to pointer size.
			unsigned Width = Index->getType()->getIntegerBitWidth();
			if (PointerSize > Width)
				SExtBits += PointerSize - Width;

			// Use GetLinearExpression to decompose the index into a C1*V+C2 form.
			APInt IndexScale(Width, 0), IndexOffset(Width, 0);
			bool NSW = true, NUW = true;
			const Value *OrigIndex = Index;
			Index = GetLinearExpression(Index, IndexScale, IndexOffset, ZExtBits,
																	SExtBits, DL, 0, AC, DT, NSW, NUW);

			// The GEP index scale ("Scale") scales C1*V+C2, yielding (C1*V+C2)*Scale.
			// This gives us an aggregate computation of (C1*Scale)*V + C2*Scale.

			// It can be the case that, even through C1*V+C2 does not overflow for
			// relevant values of V, (C2*Scale) can overflow. In that case, we cannot
			// decompose the expression in this way.
			//
			// FIXME: C1*Scale and the other operations in the decomposed
			// (C1*Scale)*V+C2*Scale can also overflow. We should check for this
			// possibility.
			APInt WideScaledOffset = IndexOffset.sextOrTrunc(MaxPointerSize*2) *
																 Scale.sext(MaxPointerSize*2);
			if (WideScaledOffset.getMinSignedBits() > MaxPointerSize) {
				Index = OrigIndex;
				IndexScale = 1;
				IndexOffset = 0;

				ZExtBits = SExtBits = 0;
				if (PointerSize > Width)
					SExtBits += PointerSize - Width;
			} else {
				Decomposed.OtherOffset += IndexOffset.sextOrTrunc(MaxPointerSize) * Scale;
				Scale *= IndexScale.sextOrTrunc(MaxPointerSize);
			}

			// If we already had an occurrence of this index variable, merge this
			// scale into it.	For example, we want to handle:
			//	 A[x][x] -> x*16 + x*4 -> x*20
			// This also ensures that 'x' only appears in the index list once.
			for (unsigned i = 0, e = Decomposed.VarIndices.size(); i != e; ++i) {
				if (Decomposed.VarIndices[i].V == Index &&
						Decomposed.VarIndices[i].ZExtBits == ZExtBits &&
						Decomposed.VarIndices[i].SExtBits == SExtBits) {
					Scale += Decomposed.VarIndices[i].Scale;
					Decomposed.VarIndices.erase(Decomposed.VarIndices.begin() + i);
					break;
				}
			}

			// Make sure that we have a scale that makes sense for this target's
			// pointer size.
			Scale = adjustToPointerSize(Scale, PointerSize);

			if (!!Scale) {
				VariableGEPIndex Entry = {Index, ZExtBits, SExtBits, Scale};
				Decomposed.VarIndices.push_back(Entry);
			}
		}

		// Take care of wrap-arounds
		if (GepHasConstantOffset) {
			Decomposed.StructOffset =
					adjustToPointerSize(Decomposed.StructOffset, PointerSize);
			Decomposed.OtherOffset =
					adjustToPointerSize(Decomposed.OtherOffset, PointerSize);
		}

		// Analyze the base pointer next.
		V = GEPOp->getOperand(0);
	} while (--MaxLookup);

	// If the chain of expressions is too deep, just return early.
	Decomposed.Base = V;
	//SearchLimitReached++;
	return true;
}

void PMRobustness::printMap(state_t * map) {
	errs() << "### Printing Map\n";
	if (map == NULL) {
		errs() << "NULL Map\n";
		return;
	}

	if (map->empty()) {
		errs() << "Empty Map\n";
		return;
	}

	for (state_t::iterator it = map->begin(); it != map->end(); it++) {
		ob_state_t *object_state = it->second;
		errs() << "#loc: " << *it->first << "\n";
		object_state->dump();
	}

	errs() << "\n***\n";
}

void PMRobustness::test() {
	typedef DenseMap<int *, int *> type_t;
	type_t * map = new type_t();

	int *x = new int(2);
	int *y = new int(3);

	(*map)[x] = x;
	(*map)[y] = y;

	errs() << "x: " << *x << "\n";
	delete map;
	errs() << "x: " << *x << "\n";
}

char PMRobustness::ID = 0;
static RegisterPass<PMRobustness> X("pmrobust", "Persistent Memory Robustness Analysis Pass");

// Automatically enable the pass.
static void registerPMRobustness(const PassManagerBuilder &,
							legacy::PassManagerBase &PM) {
	PM.add(createPromoteMemoryToRegisterPass());
	PM.add(createEarlyCSEPass(false));
	PM.add(createCFGSimplificationPass());
	PM.add(createGVNPass());
	PM.add(new PMRobustness());
}
/* Enable the pass when opt level is greater than 0 */
// Module pass cannot be scheduled with EP_EarlyAsPossible
static RegisterStandardPasses 
	RegisterMyPass1(PassManagerBuilder::EP_ModuleOptimizerEarly,
registerPMRobustness);

/* Enable the pass when opt level is 0 */
// Don't turn this on when using EP_EarlyAsPossible. Otherwise, the pass will run twice
static RegisterStandardPasses
	RegisterMyPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
registerPMRobustness);
