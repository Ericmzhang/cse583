#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;

namespace {

struct SpecPMT : public ModulePass {
    static char ID;

    SpecPMT() : ModulePass(ID) {}

    bool runOnModule(Module &M) override {

        LLVMContext &C = M.getContext();

        Type *VoidTy = Type::getVoidTy(C);
        Type *I8Ty = Type::getInt8Ty(C);
        Type *I8Ptr = Type::getInt8PtrTy(C);
        Type *I64Ty = Type::getInt64Ty(C);

        errs() << "\n[SpecPMT] Running module: " << M.getName() << "\n";

        // =====================================================
        // Declare runtime functions (LLVM 8 style)
        // =====================================================
        Function *TxBegin = cast<Function>(
            M.getOrInsertFunction(
                "pmem_tx_begin",
                FunctionType::get(VoidTy, false)
            )
        );

        Function *SpecWrite = cast<Function>(
            M.getOrInsertFunction(
                "pmem_spec_write",
                FunctionType::get(
                    VoidTy,
                    {I8Ptr, I8Ptr, I64Ty},
                    false
                )
            )
        );

        // =====================================================
        // Instrumentation
        // =====================================================
        for (Function &F : M) {
            if (F.isDeclaration()) continue;

            errs() << "  Function: " << F.getName() << "\n";

            for (BasicBlock &BB : F) {
                for (auto it = BB.begin(); it != BB.end(); ) {

                    Instruction *I = &*it++;
                    StoreInst *SI = dyn_cast<StoreInst>(I);
                    if (!SI) continue;

                    errs() << "[Instrument] store found\n";
                    errs() << "\n[DEBUG] Raw instruction:\n";
                    I->print(errs());
                    errs() << "\n";
                    IRBuilder<> B(SI);

                    // create runtime args
                    Value *addr = B.CreateBitCast(
                        SI->getPointerOperand(),
                        Type::getInt8PtrTy(M.getContext())
                    );

                    Value *val = SI->getValueOperand();

                    AllocaInst *tmp = B.CreateAlloca(val->getType());
                    B.CreateStore(val, tmp);

                    Value *val_i8 = B.CreateBitCast(
                        tmp,
                        Type::getInt8PtrTy(M.getContext())
                    );

                    Value *len = ConstantInt::get(Type::getInt64Ty(M.getContext()), 8);

                    // 🔥 IMPORTANT: insert BEFORE store (NOT after)
                    IRBuilder<> CallBuilder(SI);

                    CallBuilder.CreateCall(SpecWrite, {addr, val_i8, len});
                    errs() << "[DEBUG] Inserted call instruction\n";

                    errs() << "[DEBUG] BasicBlock now:\n";
                    BB.print(errs());
                    errs() << "\n";
                }
            }
        }

        return true; // modified module
    }
};

}

char SpecPMT::ID = 0;

static RegisterPass<SpecPMT> X(
    "specpmt",
    "SpecPMT instrumentation pass (LLVM8 compatible)"
);