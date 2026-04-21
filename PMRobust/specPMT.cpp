#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InlineAsm.h"

using namespace llvm;

namespace {

struct SpecPMT : public ModulePass {
    static char ID;

    SpecPMT() : ModulePass(ID) {}

    // =====================================================
    // Runtime function pointers (LLVM 8 safe)
    // =====================================================
    Function *TxBegin;
    Function *SpecWrite;
    Function *TxCommit;
    Function *PmemInit;

    // =====================================================
    // Detect inline asm fences / flushes (LLVM 8 safe)
    // =====================================================
    bool isFenceOrFlush(Instruction *I) {
        if (auto *CI = dyn_cast<CallInst>(I)) {
            if (CI->isInlineAsm())
                return true; // safest LLVM-8 assumption
        }
        return false;
    }

    // =====================================================
    // Identify PMRobust-protected store
    // Store must be followed by fence/flush within small window
    // =====================================================
    bool isPMWrite(StoreInst *SI) {
        Instruction *I = SI->getNextNode();

        int lookahead = 6;
        while (I && lookahead--) {

            if (isFenceOrFlush(I))
                return true;

            if (isa<StoreInst>(I))
                return false;

            I = I->getNextNode();
        }

        return false;
    }

   bool runOnModule(Module &M) override {

        LLVMContext &C = M.getContext();

        Type *VoidTy = Type::getVoidTy(C);
        Type *I8Ptr  = Type::getInt8PtrTy(C);
        Type *I64Ty  = Type::getInt64Ty(C);

        errs() << "\n[SpecPMT] Running module: " << M.getName() << "\n";

        // =====================================================
        // Runtime declarations (LLVM 8 SAFE)
        // =====================================================
        Constant *TxBegin = M.getOrInsertFunction(
            "pmem_tx_begin",
            FunctionType::get(VoidTy, false)
        );

        Constant *TxCommit = M.getOrInsertFunction(
            "pmem_commit",
            FunctionType::get(VoidTy, false)
        );

        Constant *SpecWrite = M.getOrInsertFunction(
            "pmem_spec_write",
            FunctionType::get(VoidTy, {I8Ptr, I8Ptr, I64Ty}, false)
        );

        Constant *PmemInit = M.getOrInsertFunction(
            "pmem_init",
            FunctionType::get(VoidTy, {I8Ptr, I64Ty}, false)
        );

        // =====================================================
        // Insert pmem_init at program start
        // =====================================================
        Function *Main = M.getFunction("main");
        if (Main && !Main->isDeclaration()) {

            IRBuilder<> B(&*Main->getEntryBlock().getFirstInsertionPt());

            Value *path = B.CreateGlobalStringPtr("/pmem/test_data");
            Value *size = ConstantInt::get(I64Ty, 4096);

            B.CreateCall(PmemInit, {path, size});

            errs() << "[SpecPMT] Inserted pmem_init\n";
        }

        // =====================================================
        // Instrument functions
        // =====================================================
       for (Function &F : M) {

            if (F.isDeclaration())
                continue;

            errs() << "  Function: " << F.getName() << "\n";

            bool insertedTxBegin = false;
            bool hasPMWrites = false;

            for (BasicBlock &BB : F) {
                std::vector<Instruction*> toErase;
                for (auto it = BB.begin(); it != BB.end(); ) {

                    Instruction *I = &*it++;

                    StoreInst *SI = dyn_cast<StoreInst>(I);
                    if (!SI)
                        continue;

                    if (!isPMWrite(SI))
                        continue;

                    

                    // ----------------------------
                    // STRICT PATTERN CHECK:
                    // store -> flush -> fence
                    // ----------------------------
                    Instruction *flushInst = nullptr;
                    Instruction *fenceInst = nullptr;

                    Instruction *next = SI->getNextNode();
                    if (!next) continue;

                    // ---- check FLUSH (1st step) ----
                    if (auto *CI = dyn_cast<CallInst>(next)) {

                        if (CI->isInlineAsm()) {
                            flushInst = next; // xsaveopt case
                        }
                        else if (Function *CF = CI->getCalledFunction()) {
                            StringRef name = CF->getName();
                            if (name.contains("clflush") ||
                                name.contains("flush") ||
                                name.contains("xsaveopt")) {
                                flushInst = next;
                            }
                        }
                    }

                    if (!flushInst)
                        continue;

                    // ---- check FENCE (2nd step) ----
                    next = flushInst->getNextNode();
                    if (!next)
                        continue;

                    if (auto *CI = dyn_cast<CallInst>(next)) {

                        if (CI->isInlineAsm()) {
                            fenceInst = next;
                        }
                        else if (Function *CF = CI->getCalledFunction()) {
                            StringRef name = CF->getName();
                            if (name.contains("sfence") ||
                                name.contains("fence")) {
                                fenceInst = next;
                            }
                        }
                    }

                    if (!fenceInst)
                        continue;

                    errs() << "[SpecPMT] matched store+flush+fence\n";
                    hasPMWrites = true;
                    // ----------------------------
                    // Instrument replacement
                    // ----------------------------
                    IRBuilder<> B(SI);

                    if (!insertedTxBegin) {
                        B.CreateCall(TxBegin);
                        insertedTxBegin = true;
                    }

                    Value *addr = B.CreateBitCast(SI->getPointerOperand(), I8Ptr);

                    Value *val = SI->getValueOperand();

                    AllocaInst *tmp = B.CreateAlloca(val->getType());
                    B.CreateStore(val, tmp);
                    Value *valPtr = B.CreateBitCast(tmp, I8Ptr);

                    Value *len = ConstantInt::get(I64Ty, 8);

                    B.CreateCall(SpecWrite, {addr, valPtr, len});

                    // ----------------------------
                    // erase original sequence
                    // ----------------------------
                    toErase.push_back(SI);
                    toErase.push_back(flushInst);
                    toErase.push_back(fenceInst);
                }
                
                for (Instruction *I : toErase) {
                    if (I && I->getParent()) {
                        I->eraseFromParent();
                    }
                }
                toErase.clear(); 
            }
            // commit only if needed
            if (hasPMWrites) {
                IRBuilder<> B(&*F.getEntryBlock().getTerminator());
                B.CreateCall(TxCommit);
            }
        }

        return true;
    }
};

} // namespace

char SpecPMT::ID = 0;

static RegisterPass<SpecPMT> X(
    "specpmt",
    "LLVM-8 safe PMRobust-aware SpecPMT pass",
    false,
    false
);