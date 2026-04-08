#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IRBuilder.h"

using namespace llvm;

#define FLUSH_SIZE 64
#define ASM_CLFLUSH "clflush $0"
#define ASM_CLFLUSHOPT ".byte 0x66; clflush $0"
#define ASM_CLWB ".byte 0x66; xsaveopt $0"
#define ASM_SFENCE "sfence"
#define MAX_RANGE_FLUSH (64 * 64)

enum FlushInst {
    CLWB_INST, CLFLUSHOPT_INST, CLFLUSH_INST
};

static cl::opt<FlushInst> flushInst("flush-inst", cl::desc("Choose flush instruction"),
  cl::values(
    clEnumValN(CLWB_INST, "clwb", "use clwb as PM flush instruction"),
    clEnumValN(CLFLUSHOPT_INST, "clflushopt", "use clflushopt as PM flush instruction"),
    clEnumValN(CLFLUSHOPT_INST, "clflush", "use clflush as PM flush instruction")), 
  cl::init(CLWB_INST));

inline StringRef FlushInst2ASM(FlushInst inst) {
    switch(inst) {
    case CLWB_INST:
        return ASM_CLWB;
    case CLFLUSHOPT_INST:
         return ASM_CLFLUSHOPT;
    case CLFLUSH_INST:
         return ASM_CLFLUSH;
    }
}

static CallInst *insertFlush(IRBuilder<> &builder, Value *target, unsigned offset = 0) {
    assert(target->getType()->isPointerTy());
    StringRef flush = FlushInst2ASM(flushInst);
    StringRef constraint = "=*m,*m,~{dirflag},~{fpsr},~{flags}";

    std::vector<Type*> argTy = {target->getType(), target->getType()};
    std::vector<Value*> args = {target, target};

    Type* voidty = builder.getVoidTy();
    FunctionType* functy = FunctionType::get(voidty, argTy, false);
    InlineAsm *asmcall = InlineAsm::get(functy, flush, constraint, 
            true, false);

    //errs() << "insert flush to " << *target << " before " << *I << " at offset " << offset << "\n";
    if (offset > 0) {
        auto pti = builder.CreatePtrToInt(target, builder.getInt64Ty());
        auto add = builder.CreateAdd(pti, ConstantInt::get(builder.getInt64Ty(), offset));
        auto itp = builder.CreateIntToPtr(add, target->getType());
        args = {itp, itp};
    }
    return builder.CreateCall(functy, asmcall, args);
}

static CallInst *insertFlushRange(IRBuilder<> &builder, Value *target, unsigned start, unsigned len) {
    CallInst *ret = nullptr;
    auto end = start + len;
    for (unsigned i = start; i < end; i+= FLUSH_SIZE) {
        ret = insertFlush(builder, target, i);
    }
    return ret;
}

static CallInst *insertSFence(IRBuilder<> &builder) {
    Type* voidty = builder.getVoidTy();
    FunctionType* functy = FunctionType::get(voidty, {}, false);
    InlineAsm *asmcall = InlineAsm::get(functy, ASM_SFENCE,"~{memory},~{dirflag},~{fpsr},~{flags}" , true, false);
    return builder.CreateCall(functy, asmcall, {});
}

