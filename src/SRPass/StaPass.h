// This file is part of ASAP.
// Please see LICENSE.txt for copyright and licensing information.

#include "llvm/Pass.h"

#include <utility>
#include <vector>
#include <map>
#include <set>

namespace sanitychecks {
    class GCOVFile;
}

namespace llvm {
    class BranchInst;
    class raw_ostream;
    class Instruction;
    class Value;
}

struct SCIPass;

struct StaPass : public llvm::ModulePass {
    static char ID;
    std::map<llvm::Instruction*,llvm::Instruction*> ReducedInst;

    StaPass() : ModulePass(ID) {}

    virtual bool runOnModule(llvm::Module &M);

    virtual void getAnalysisUsage(llvm::AnalysisUsage& AU) const;
    
    void optimizeCheckAway(llvm::Instruction *Inst);
    bool findSameSource(llvm::Instruction *BI1, llvm::Instruction *BI2, uint64_t id1, uint64_t id2, uint64_t flag);
    std::set<llvm::Value*> TrackMemoryLoc(llvm::Instruction *C, uint64_t id);
    bool SameMemoryLoc(std::set<llvm::Value*> FClist1, std::set<llvm::Value*> FClist2, uint64_t id1, uint64_t id2);

private:

    SCIPass *SCI;
};
