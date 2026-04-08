#ifndef LLVM_LIB_ANALYSIS_TAINT_KNOWN_FUNCTIONS_CONFIG_H
#define LLVM_LIB_ANALYSIS_TAINT_KNOWN_FUNCTIONS_CONFIG_H

#include <cstdint>
#include <stdlib.h>

//#define ALL_ALLOC_FN_PMEM 1
//#define UNKNOWN_ESCAPED_PMEM 1

struct NameAnnoPair {
    std::string FnName;
    std::string Anno;
};

static const std::string PMAllocAnno = "pm_allocator";

//A pm_allocator annotation has the format
// OPERAND = "r" | "0" | "1" | "2" | ....
// LEVEL = "0" | "1" | "2" | ...
// ANNO = OPERAND "," LEVEL
// ANNOS = ANNO ("|" ANNO)+
// where the operand r stands for return value, 0 stands for the first argument, 1 the second argument etc.
// the levels stand for the pointer dereference level
static const NameAnnoPair PMAllocatorAnnos[] = {
	//libpmem
	NameAnnoPair{"pmem_map_file", "r,0"},
	//pmdk/common
	NameAnnoPair{"util_map_sync", "r,0"},
	//libpmemobj
	NameAnnoPair{"_ZL21pmemobj_direct_inline7pmemoid", "r,0"},  //pmemobj_direct_inline(pmemoid)
	//libpmemobj
	NameAnnoPair{"pmemobj_direct_inline", "r,0"},  //pmemobj_direct_inline(pmemoid)
	//general purpose
	NameAnnoPair{"mmap", "r,0|0,0"},
	//libpmem2
	NameAnnoPair{"file_map", "6,1"},
};
#endif //LLVM_LIB_ANALYSIS_TAINT_KNOWN_FUNCTIONS_CONFIG_H
