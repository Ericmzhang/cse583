#include "llvm/IR/IRBuilder.h"
#include "llvm/ADT/BitVector.h"
#include "FunctionSummary.h"
#include <cassert>

using namespace llvm;

#define UNKNOWNOFFSET 0xffffffff
#define VARIABLEOFFSET 0xfffffffe
//#define FUNC_PARAM_USE 100

struct ob_state_t;
struct ArrayInfo;

typedef DenseMap<const Value *, ob_state_t *> state_t;
typedef DenseMap<const Instruction *, state_t> state_map_t;
typedef DenseMap<const BasicBlock *, state_t> b_state_map_t;
typedef DenseMap<const Value *, ArrayInfo> addr_set_t;

typedef DenseSet<Value *> value_set_t;
typedef DenseMap<const Value *, value_set_t *> alias_set_t;

enum NVMOP {
	NVM_CLWB,
	NVM_CLFLUSH,
	NVM_FENCE,
	NVM_UNKNOWN
};

struct VariableGEPIndex {
	// An opaque Value - we can't decompose this further.
	const Value *V;

	// We need to track what extensions we've done as we consider the same Value
	// with different extensions as different variables in a GEP's linear
	// expression;
	// e.g.: if V == -1, then sext(x) != zext(x).
	unsigned ZExtBits;
	unsigned SExtBits;

	APInt Scale;

	bool operator==(const VariableGEPIndex &Other) const {
		return V == Other.V && ZExtBits == Other.ZExtBits &&
					 SExtBits == Other.SExtBits && Scale == Other.Scale;
	}

	bool operator!=(const VariableGEPIndex &Other) const {
		return !operator==(Other);
	}
};

struct DecomposedGEP {
	// Base pointer of the GEP
	const Value *Base;
	// Total constant offset w.r.t the base from indexing into structs
	APInt StructOffset;
	// Total constant offset w.r.t the base from indexing through
	// pointers/arrays/vectors
	APInt OtherOffset;
	// Scaled variable (non-constant) indices.
	SmallVector<VariableGEPIndex, 4> VarIndices;

	bool isArray;

	uint64_t getOffsets() {
		if (VarIndices.size() == 0) {
			assert(StructOffset.getSExtValue() >= 0);
			//assert(OtherOffset.getSExtValue() >= 0);
			if (OtherOffset.getSExtValue() < 0) {
#ifdef PMROBUST_DEBUG
				errs() << "strange offset: " << StructOffset.getSExtValue() << ", " << OtherOffset.getSExtValue() << "\n";
#endif
				return UNKNOWNOFFSET;
			}

			uint64_t offset = StructOffset.getZExtValue() + OtherOffset.getZExtValue();
			return offset;
		} else
			return VARIABLEOFFSET;
	}

	uint64_t getStructOffset() {
		assert(StructOffset.getSExtValue() >= 0);
		return StructOffset.getZExtValue();
	}
};

struct ArrayInfo {
	// `state` should only record dirty/clwb states, with possible values be
	// DIRTY_ESCAPED or CLWB_ESCAPED
	// Escapedness is recored in other places
	ParamStateType state;
	const Value *Base;

	ArrayInfo() {
		Base = nullptr;
	}

	ParamStateType getState() {
		return state;
	}

	void set(ParamStateType s, const Value *B) {
		if (Base != nullptr)
			assert(Base == B);

		state = s;
		Base = B;
	}

	void setState(ParamStateType s) {
		state = s;
	}

	void copyFrom(ArrayInfo &other) {
		Base = other.Base;
		state = other.state;
	}

	void mergeFrom(ArrayInfo &other) {
		// TODO
		assert(Base == other.Base);
		if (state == ParamStateType::DIRTY_ESCAPED || other.state == ParamStateType::DIRTY_ESCAPED)
			state = ParamStateType::DIRTY_ESCAPED;
		else if(state == ParamStateType::CLWB_ESCAPED || other.state == ParamStateType::CLWB_ESCAPED)
			state = ParamStateType::CLWB_ESCAPED;
	}
};

static inline std::string getPosition(const Instruction * I, bool print = false)
{
	const DebugLoc & debug_location = I->getDebugLoc ();
	std::string position_string;
	{
		llvm::raw_string_ostream position_stream (position_string);
		debug_location.print (position_stream);
	}

	// Phi instructions do not have positions
	// TODO: some instructions have position:0

	if (print) {
		errs() << position_string << "\n";
	}

	return position_string;
}

bool checkPosition(Instruction * I, IRBuilder <> IRB, std::string sub)
{
	const DebugLoc & debug_location = I->getDebugLoc ();
	std::string position_string;
	{
		llvm::raw_string_ostream position_stream (position_string);
		debug_location . print (position_stream);
	}

	std::size_t found = position_string.find(sub);
	if (found!=std::string::npos)
		return true;

	return false;
}

static void printBitVectorAsIntervals(BitVector BV) {
	int IntervalStart = -1; //-1 if not in a strip of ones
	for (unsigned i = 0; i < BV.size(); i++) {
		if (BV[i] && IntervalStart == -1)
			IntervalStart = i;
		if ((!BV[i] || i+1 == BV.size()) && IntervalStart != -1) {
			errs() << IntervalStart << " - " << i << ", ";
			IntervalStart = -1;
		}
	}

}

static const unsigned max_size = 8192;
/**
 * TODO: may need to track the size of fields
 **/
// <dirty_byte, clwb_byte> is either <0, 0>, <1, 0>, or <1, 1>
class ob_state_t {
private:
	unsigned size;
	BitVector dirty_bytes;
	BitVector clwb_bytes;
	bool escaped;
	bool nonpmem;
	bool is_array;
	// the position where the state most recently
	// changes to dirty/escaped
	// empty from not dirty/escaped
	Instruction* dirty_pos = nullptr;
	Instruction* escaped_pos = nullptr; 
	bool mark_delete;
	
	void resize(unsigned s) {
		if (size >= s)
			return;

		assert(s <= max_size && "oversize s");
		size = s;
		dirty_bytes.resize(s);
		clwb_bytes.resize(s);
	}

public:
	ob_state_t() :
		size(0),
		dirty_bytes(),
		clwb_bytes(),
		escaped(false),
		nonpmem(false),
		is_array(false),
		mark_delete(false)
	{}

	ob_state_t(unsigned s) :
		escaped(false),
		nonpmem(false),
		is_array(false),
		mark_delete(false)
	{ 
		s = std::min(s, max_size);
		size = s;
		dirty_bytes.resize(s);
		clwb_bytes.resize(s);
	}

	ob_state_t(ob_state_t * other) :
		size(other->size),
		dirty_bytes(other->dirty_bytes),
		clwb_bytes(other->clwb_bytes),
		escaped(other->escaped),
		nonpmem(other->nonpmem),
		is_array(other->is_array),
		dirty_pos(other->dirty_pos),
		escaped_pos(other->escaped_pos),
		mark_delete(false)
	{}

    void mergeFrom(ob_state_t * other) {
		//assert(size == other->size);

		// <dirty_byte, clwb_byte> is either <0, 0>, <1, 0>, or <1, 1>
		// clwb_bytes = (clwb_bytes | other->clwb_bytes) &
		// ~((dirty_bytes ^ clwb_bytes) | (other->dirty_bytes ^ other->clwb_bytes));
		// dirty_bytes = dirty_bytes | other->dirty_bytes
		if (other->size > size)
			size = other->size;

		BitVector tmp1(dirty_bytes);
		BitVector tmp2(other->dirty_bytes);
		tmp1 ^= clwb_bytes;
		tmp2 ^= other->clwb_bytes;
		tmp1 |= tmp2;
		tmp1.flip();
		clwb_bytes |= other->clwb_bytes;
		clwb_bytes &= tmp1;

		dirty_bytes |= other->dirty_bytes;

		escaped |= other->escaped;
		nonpmem &= other->nonpmem;
		is_array |= other->is_array;
	}

	void copyFrom(ob_state_t * src) {
		//assert(size == src->size);

		size = src->size;
		dirty_bytes = src->dirty_bytes;
		clwb_bytes = src->clwb_bytes;
		escaped = src->escaped;

//		if (nonpmem != src->nonpmem) {
//			assert(false);
//		}

		// nonpmem comes from Calling Contexts, which can be different
		// Since only the initial state is reset each time analyzing functions,
		// we propagate nonpmem by copying
		nonpmem = src->nonpmem;
		is_array = src->is_array;
        
		escaped_pos = src->escaped_pos;
		dirty_pos = src->dirty_pos;
	}

	void resetDirtyEscapedPos(Instruction *pos) {
		escaped_pos = pos;
		dirty_pos = pos;
	}

	bool copyFromCheckDiff(ob_state_t * src, bool update_pos = true) {
		bool updated = false;
		updated |= (size != src->size);
		updated |= (dirty_bytes != src->dirty_bytes);
		updated |= (clwb_bytes != src->clwb_bytes);
		updated |= (escaped != src->escaped);
		updated |- (is_array != src->is_array);

		size = src->size;
		dirty_bytes = src->dirty_bytes;
		clwb_bytes = src->clwb_bytes;
		escaped = src->escaped;

		// nonpmem comes from Calling Contexts, and is not considered as a change in states
		nonpmem = src->nonpmem;
		is_array = src->is_array;

        	if(update_pos) {
        	    // should change in pos be counted in update?
			escaped_pos = src->escaped_pos;
			dirty_pos = src->dirty_pos;
        	}
		return updated;
	}
        
	void setToArray() {
                is_array = true;
                bool anyDirty = dirty_bytes.any();
                bool anyClwb = clwb_bytes.any();
                dirty_bytes.resize(1);
                clwb_bytes.resize(1);
                if (anyDirty)
                        dirty_bytes.set();
                if (anyClwb)
                        clwb_bytes.set();
	}

	// return true: modified; return else: un)changed
	bool setDirty(unsigned start, unsigned len, Instruction *new_dirty_pos) {
		if (nonpmem)
			return false;

                if (is_array) {
                        bool ret = dirty_bytes.none() || clwb_bytes.any();
                        dirty_bytes.set();
                        clwb_bytes.reset();
                        return ret;
                }

		unsigned end = start + len;
		start = std::min(start, max_size);
		end = std::min(end, max_size);
		if (end > size) {
			resize(end);
		}
                
		//errs() << "start: " << start << "; len: " << len << "; end:" << end << "\n";
		//errs() << "actual size: " << size << "\n";
		int index1 = dirty_bytes.find_first_unset_in(start, end);
		int index2 = clwb_bytes.find_first_in(start, end);

		// dirty_byte are all 1 and clwb_bytes are all 0, then no change
		if (index1 == -1 && index2 == -1)
			return false;

        	dirty_pos = new_dirty_pos;
		dirty_bytes.set(start, end);
		clwb_bytes.reset(start, end);	

		return true;
	}

	// Check if there are other nonclean (dirty or clwb) bytes other than the ones in [start, end)
	bool hasNoncleanBytesNotIn(unsigned start, unsigned len) {
		if (nonpmem)
			return false;

                //conservatively true for arrays
                if (is_array)
                        return true;

		unsigned end = start + len;
		start = std::min(start, max_size);
		end = std::min(end, max_size);
		if (end > size) {
			resize(end);
		}

		int setBitBeforeStart = dirty_bytes.find_first_in(0, start);
		int setBitAfterEnd = dirty_bytes.find_first_in(end, dirty_bytes.size());

		if (setBitBeforeStart == -1 && setBitAfterEnd == -1)
			return false;

		return true;
	}

	bool MultipleNoncleanFieldsBadApproximation() {
		if (nonpmem)
			return false;

		unsigned j = dirty_bytes.size() / 8;
		if (dirty_bytes.size() % 8 != 0)
			j++;

		int dirty_count = 0;
		for (unsigned i = 0; i < j; i++) {
			unsigned start = i * 8;
			unsigned end = (i + 1) * 8;
			if (end >= dirty_bytes.size())
				end = dirty_bytes.size();
/*
			if (dirty_bytes.find_first_in(start, end) != -1) {
				dirty_count++;

				if (dirty_count >= 2) {
					return true;
				}
			}
*/
		}

		return false;
	}

	// TODO: start + len and size?
	// Flush wrapper function may flush cache lines exceeding the size of this object
	bool setFlush(unsigned start, unsigned len, bool onlyFlushWrittenBytes = false) {
		if (nonpmem)
			return false;

                if (is_array) {
                        bool ret = dirty_bytes.any() || clwb_bytes.any();
                        dirty_bytes.reset();
                        clwb_bytes.reset();
                        return ret;
                }

		if (start > size && onlyFlushWrittenBytes) {
			errs() << "FIXME: Flush unknown bytes\n";
			return false;
			//assert(false && "Flush unknown bytes");
		}

		unsigned end = start + len;
		start = std::min(start, max_size);
		end = std::min(end, max_size);
		if (len == (unsigned)-1 && onlyFlushWrittenBytes) {
			// start + len may overflow
			end = size;
		} else if (end > size && onlyFlushWrittenBytes) {
			end = size;
		} else if (end > size)
			resize(end);
 
		int index1 = dirty_bytes.find_first_in(start, end);
		int index2 = clwb_bytes.find_first_in(start, end);

		// dirty_byte and clwb_bytes are all 0, then no change
		if (index1 == -1 && index2 == -1)
			return false;

		dirty_bytes.reset(start, end);
		clwb_bytes.reset(start, end);

		return true;
	}

	// TODO: start + len and size?
	// Flush wrapper function may flush cache lines exceeding the size of this object
	bool setClwb(unsigned start, unsigned len, bool onlyFlushWrittenBytes = false) {
		if (nonpmem)
			return false;

                if (is_array) {
                        bool old = clwb_bytes.any();
                        if (dirty_bytes.any())
                                clwb_bytes.set();
                        return !old && clwb_bytes.any();
                }
 
		if (start > size && onlyFlushWrittenBytes) {
			errs() << "FIXME: Clwb unknown bytes\n";
			return false;
			//assert(false && "Clwb unknown bytes");
		}

		unsigned end = start + len;		
		start = std::min(start, max_size);
		end = std::min(end, max_size);
		if (end > size && onlyFlushWrittenBytes) {
			end = size;
		} else if (end > size)
			resize(end);

		// set clwb_bytes for bytes in dirty_bytes
		BitVector tmp(dirty_bytes);
		tmp.reset(0, start);
		tmp.reset(end, tmp.size());

		BitVector old_clwb_bytes(clwb_bytes);
		clwb_bytes |= tmp;
		
        	if (old_clwb_bytes == clwb_bytes)
			return false;	// No change

		return true;
	}

	// apply Fence on clwb bytes
	bool applyFence() {
		if (clwb_bytes.any()) {
			dirty_bytes ^= clwb_bytes;
			clwb_bytes.reset();
			return true;
		}

		return false;
	}

	// return true: modified; return else: unchanged
	bool setEscape(Instruction *new_escaped_pos) {
        	escaped_pos = new_escaped_pos;
		if (escaped == false) {
			escaped = true;
			return true;
		}

		return false;
	}

	bool setCaptured() {
		if (escaped == true) {
			escaped = false;
			return true;
		}

		return false;
	}

	bool isEscaped() {
		return escaped;
	}

	void setNonPmem() {
		nonpmem = true;
	}

	bool isNonPmem() {
		return nonpmem;
	}

	void markDelete() {
		mark_delete = true;
	}

	void unmarkDelete() {
		mark_delete = false;
	}

	bool shouldDelete() {
		return mark_delete;
	}

	unsigned getSize() {
		return size;
	}

	void setSize(unsigned s) {
		size = s;
	}

	ParamStateType checkState() {
		return checkState(0, size);
	}

	ParamStateType checkState(unsigned startByte, unsigned len) {
		if (is_array) {
			startByte = 0;
			len = 1;
		}

		unsigned endByte = startByte + len;
		//errs() << "range: " << startByte << " - " << startByte + len << "; size: " << size << "\n";

		if (size == 0) {
			if (escaped)
				return ParamStateType::CLEAN_ESCAPED;
			else
				return ParamStateType::TOP;
		}

		startByte = std::min(startByte, max_size);
		endByte = std::min(endByte, max_size);

		if (startByte >= size) {
			errs() << "Checking state out of range\n";
			errs() << "range: " << startByte << " - " << startByte + len << "; size: " << size << "\n";
			return ParamStateType::TOP;
			//assert(false);
		}

		if (endByte > size)
			endByte = size;

		BitVector tmp(dirty_bytes);
		tmp &= clwb_bytes;

		if (escaped) {
			if (dirty_bytes.find_first_in(startByte, endByte) == -1) {
				// dirty_bytes are all 0
				return ParamStateType::CLEAN_ESCAPED;
			} else if (dirty_bytes == tmp) {
				// all set dirty_bytes are clwbed;
				return ParamStateType::CLWB_ESCAPED;
			} else {
				// Some set dirty_bytes are not clwbed
				return ParamStateType::DIRTY_ESCAPED;
			}
		} else {
			if (dirty_bytes.find_first_in(startByte, endByte) == -1) {
				// dirty_bytes are all 0
				return ParamStateType::CLEAN_CAPTURED;
			} else if (dirty_bytes == tmp) {
				// all set dirty_bytes are clwbed;
				return ParamStateType::CLWB_CAPTURED;
			} else {
				// Some set dirty_bytes are not clwbed
				return ParamStateType::DIRTY_CAPTURED;
			}
		}
	}

	bool isDirty() {
		for (auto Itr = dirty_bytes.set_bits_begin(); Itr != dirty_bytes.set_bits_end(); Itr++)
			if(!clwb_bytes.test(*Itr))
				return true;

		return false;
	}

	bool isClwb() {
		return clwb_bytes.any();
	}

	void computeDirtyBytes(DirtyBytesInfo &info) {
		//dump();

		BitVector only_dirty_bytes(dirty_bytes);
		only_dirty_bytes ^= clwb_bytes;

		int i = only_dirty_bytes.find_first();

		while (i != -1) {
			// Store [i, j)
			int j = only_dirty_bytes.find_next_unset(i);

			if (j == -1) {
				j = only_dirty_bytes.size();
				info.push(i, j);
				break;
			}

			info.push(i, j);
			assert(j >= 1);
			i = only_dirty_bytes.find_next(j - 1);
		}
	}

	Instruction * getDirtyPos() {
		return dirty_pos;
	}

	Instruction * getEscapedPos() {
		return escaped_pos;
	}

	inline std::string getDirtyPosStr() {
        	if (!dirty_pos)
			return "unknown position";

		auto ret = getPosition(dirty_pos);
		if (ret.empty()) {
			llvm::raw_string_ostream position_stream (ret);
			position_stream << *dirty_pos;
	        }
		return ret;
	}

	inline std::string getEscapedPosStr() {
        	if (!escaped_pos)
			return "unknown position";

		auto ret = getPosition(escaped_pos);
		if (ret.empty()) {
			llvm::raw_string_ostream position_stream (ret);
			position_stream << *escaped_pos;
	        }
		return ret;
	}

	std::string getDirtyEscapedPosStr() {
 		return "dirty at " + getDirtyPosStr() + ", escaped at " + getEscapedPosStr();
	}

	void dump() {
		errs() << "bit vector size: " << size << "\n";
		if (size != 0) {
			if (dirty_bytes.any()) {
				errs() << "dirty bytes: ";
				printBitVectorAsIntervals(dirty_bytes);
				errs() << "\nfirst dirty at " << getDirtyPosStr() << "\n";

				errs() << "clwb bytes: ";
				printBitVectorAsIntervals(clwb_bytes);
				errs() << "\n";
			}
		}

		if (escaped)
			errs() << "escaped at " << getEscapedPosStr();
		else
			errs() << "captured";

		if (nonpmem)
			errs() << "; nonpmem";
		else
			errs() << "; pmem";
		errs() << "\n";
	}
};

void printDecomposedGEP(DecomposedGEP &Decom) {
	errs() << "Store Base: " << *Decom.Base << "\t";
	errs() << "Struct Offset: " << Decom.StructOffset << "\t";
	errs() << "Other Offset: " << Decom.OtherOffset << "\t";
	errs() << "Has VarIndices: " << Decom.VarIndices.size() << "\n";
	/*
	for (unsigned i = 0 ; i < Decom.VarIndices.size(); i++) {
		VariableGEPIndex &VI = Decom.VarIndices[i];
		errs() << *VI.V << "\n";
		errs() << "(" << VI.ZExtBits << ", " << VI.SExtBits << ")\t";
		errs() << "Scale: " << VI.Scale << "\n";
	}*/
}

/// To ensure a pointer offset fits in an integer of size PointerSize
/// (in bits) when that size is smaller than the maximum pointer size. This is
/// an issue, for example, in particular for 32b pointers with negative indices
/// that rely on two's complement wrap-arounds for precise alias information
/// where the maximum pointer size is 64b.
static APInt adjustToPointerSize(APInt Offset, unsigned PointerSize) {
    assert(PointerSize <= Offset.getBitWidth() && "Invalid PointerSize!");
    unsigned ShiftBits = Offset.getBitWidth() - PointerSize;
    return (Offset << ShiftBits).ashr(ShiftBits);
}

static unsigned getMaxPointerSize(const DataLayout &DL) {
    unsigned MaxPointerSize = DL.getMaxPointerSizeInBits();
    //if (MaxPointerSize < 64 && ForceAtLeast64Bits) MaxPointerSize = 64;
    //if (DoubleCalcBits) MaxPointerSize *= 2;

    return MaxPointerSize;
}
