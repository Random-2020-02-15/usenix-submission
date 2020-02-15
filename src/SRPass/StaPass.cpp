// This file is part of ASAP.
// Please see LICENSE.txt for copyright and licensing information.

#include "StaPass.h"
#include "SCIPass.h"
#include "utils.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Format.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"

#include <algorithm>
#include <memory>
#include <system_error>
#define DEBUG_TYPE "StaPass"

using namespace llvm;



static cl::opt<std::string>
InputSCOV("Sscov", cl::desc("<input scov file>"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
InputUCOV("Sucov", cl::desc("<input ucov file>"), cl::init(""), cl::Hidden);


bool StaPass::runOnModule(Module &m) {
    SCI = &getAnalysis<SCIPass>();
    
    std::string filename = m.getSourceFileName();
    filename = filename.substr(0, filename.rfind("."));
    

    struct tmp{
        uint64_t id;
        uint64_t count[3];
    }BrInfo;
    typedef uint64_t Info[4];
    struct stat{
        uint64_t id;
        uint64_t LB;
        uint64_t RB;
        Instruction* SC;
    };

    std::map<Instruction*, Info> SC_Stat;
    std::map<Instruction*, Info> UC_Stat;
    std::map<uint64_t, std::vector<stat>> SC_Pattern, SC_Pattern_opt;
    std::map<uint64_t, uint64_t> reducedSC;
    std::vector<Instruction*> RSC;
    int count = 0;

    FILE *fp_sc = fopen(Twine(InputSCOV).str().c_str(), "rb");
    // errs() << Twine(InputSCOV).str().c_str() << "\n";
    // assert(fp_sc != NULL && "No valid SCOV file");
    // assert(fp_uc != NULL && "No valid UCOV file");
    bool read = false;
    if (fp_sc != NULL) {
        read = true;
    }

    errs() << "StaPass on "<<filename << "\n";

    uint64_t flagSC = 0, costflagSC = 0; // Number of SCs
    uint64_t flagUC = 0, costflagUC = 0; // Number of UCs
    uint64_t flagSC_opt = 0, costflagSC_opt = 0; // Number of SCs after the redundant SCs about UCs are reduced
    uint64_t flagSC_opts = 0, costflagSC_opts = 0; // Number of SCs after the redundant SCs about SCs are reduced
    uint64_t test1 = 0, test2 = 0;
    bool is_reduced = true;

    // Start reading and storing SC coverage records from InputSCOV
    for (Function &F: m) {
        for (Instruction *Inst: SCI->getSCBranches(&F)) {
            assert(Inst->getParent()->getParent() == &F && "SCI must only contain instructions of the current function.");
            BranchInst *BI = dyn_cast<BranchInst>(Inst);
            assert(BI && BI->isConditional() && "SCBranches must not contain instructions that aren't conditional branches.");
            if (read) {
                fread(&BrInfo, sizeof(BrInfo), 1, fp_sc);
            }
            else {
                BrInfo.count[1] = 0;
                BrInfo.count[2] = 0;
            }
            // Revise the coverage pattern of SC
            // errs() <<"SC:"<<BrInfo.id << ":"<< BrInfo.count[0] <<":"<< BrInfo.count[1] <<":"<< BrInfo.count[2] << "\n";
            BrInfo.count[0] = BrInfo.count[1] + BrInfo.count[2];
            for (size_t i=0;i<3;i++){
                SC_Stat[Inst][i] = BrInfo.count[i];
            }
            SC_Stat[Inst][3] = flagSC;

            // Store the dynamic patterns of instructions in SCBranches in SC_Pattern (totalCovTime->SC_Info)
            // SC_Info contains id, LB, RB, and *Inst
            struct stat SC_Info;
            SC_Info.id = BrInfo.id;
            SC_Info.LB = BrInfo.count[1];
            SC_Info.RB = BrInfo.count[2];
            SC_Info.SC = Inst;
            SC_Pattern[BrInfo.count[0]].push_back(SC_Info);
            flagSC += 1;
            costflagSC += BrInfo.count[0];
        }
    }
    fclose(fp_sc);
    // Finish reading and storing SC coverage records from InputSCOV

    // Start reading and storing UC coverage records from InputUCOV
    // During this process, each UC will be compared with all SCs in SC_Pattern
    // For each SC in SC_Pattern, if its coverage pattern matches that of UC
    // And if the variable it operates is the same as that operated by UC
    // Then, the SC can be reduced.
    flagSC_opt = flagSC;
    costflagSC_opt = costflagSC;
    errs() <<flagSC <<":"<<costflagSC << "----\n";
    for (Function &F: m) {
        if (SCI->getUCBranches(&F).size() > 0) {
            // const DominatorTree &T = getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
            PostDominatorTree PostDT = PostDominatorTree(F);
            DominatorTree DT = DominatorTree(F);
            for (Instruction *UC: SCI->getUCBranches(&F)) {
                flagUC += 1;
                for (Instruction *SC: SCI->getUCBranches(&F)) {
                    if (UC->getParent()->getParent() == SC->getParent()->getParent()) {
                        if (DT.dominates(UC->getParent(), SC->getParent()) || PostDT.dominates(UC->getParent(), SC->getParent())) {
                            if (findSameSource(UC, SC, 0, 0, 0)) {
                                // optimizeCheckAway(SC);
                                reducedSC[SC_Stat[SC][3]] = 1;
                                flagSC_opt -= 1;
                                costflagSC_opt -= SC_Stat[SC][0];
                            }
                        }
                    }
                }
            }
        }
    }
    // Finish reading and storing UC coverage records from InputUCOV

    // Reduce redundant SCs among SCs
    // For each SC read from SCOV file
    // Check whether its pattern matches any SCs in SC_Pattern_opt
    // If it is, this SC can be reduced
    flagSC_opts = flagSC_opt;
    costflagSC_opts = costflagSC_opt;
    errs() <<flagSC_opt <<":"<<costflagSC_opt << "----\n";
    uint64_t P = 0;
    // DominatorTree T;
    for (Function &F: m) {
        if (SCI->getSCBranches(&F).size() > 0) {
            // const DominatorTree &T = getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
            PostDominatorTree PostDT = PostDominatorTree(F);
            DominatorTree DT = DominatorTree(F);
            for (Instruction *SC1: SCI->getSCBranches(&F)) {
                Instruction *SC1_tmp = SC1;
                BranchInst *BI1 = dyn_cast<BranchInst>(SC1);
                for (Instruction *CI: SCI->getInstructionsBySanityCheck(BI1)) {
                    if (BranchInst *BI_tmp = dyn_cast<BranchInst>(CI)) {
                        if (CI != SC1) {
                            SC1_tmp = BI_tmp;
                        }
                    }
                }
                for (Instruction *SC2: SCI->getSCBranches(&F)) {
                    Instruction *SC2_tmp = SC2;
                    BranchInst *BI2 = dyn_cast<BranchInst>(SC2);
                    for (Instruction *CI: SCI->getInstructionsBySanityCheck(BI2)) {
                        if (BranchInst *BI_tmp = dyn_cast<BranchInst>(CI)) {
                            if (CI != SC2) {
                                SC2_tmp = BI_tmp;
                            }
                        }
                    }
                    if (SC1_tmp->getParent()->getParent() == SC2_tmp->getParent()->getParent()) {
                        if (DT.dominates(SC2_tmp->getParent(), SC1_tmp->getParent()) && reducedSC[SC_Stat[SC1][3]] == 0) {
                            if (SC1 != SC2 && findSameSource(SC1, SC2, 0, 0, 1)) {
                                // optimizeCheckAway(Inst);
                                flagSC_opts -= 1;
                                costflagSC_opts -= SC_Stat[SC1][0];
                                reducedSC[SC_Stat[SC1][3]] = 1;
                            }
                        }
                        else if (!DT.dominates(SC1_tmp->getParent(), SC2_tmp->getParent()) && PostDT.dominates(SC2_tmp->getParent(), SC1_tmp->getParent()) && reducedSC[SC_Stat[SC1][3]] == 0) {
                            if (SC1 != SC2 && findSameSource(SC1, SC2, 0, 0, 1)) {
                                // optimizeCheckAway(Inst);
                                flagSC_opts -= 1;
                                costflagSC_opts -= SC_Stat[SC1][0];
                                reducedSC[SC_Stat[SC1][3]] = 1;
                            } 
                        }
                    }
                }
            }
        }
    }
    for (Function &F: m) {
        for (Instruction *SC: SCI->getSCBranches(&F)) {
            if (reducedSC[SC_Stat[SC][3]] == 1) {
                optimizeCheckAway(SC);
            }
        }
    }
    errs() << "UC num :: " << flagUC << ";SC Num :: " << flagSC << ";SC percent after L1 :: " << flagSC_opt * 1.0 / (flagSC+0.0001) * 100 << "\%;SC percent after L2 :: " << flagSC_opts * 1.0 / (flagSC+0.0001) * 100 << "\%\n";
    errs() << "SC cost percent:: "<< costflagSC/(costflagSC+0.0001) * 100  << ";SC cost percent after L1 :: " << costflagSC_opt * 1.0 / (costflagSC+0.0001) * 100 << "\%;SC cost percent after L2 :: " << costflagSC_opts * 1.0 / (costflagSC+0.0001) * 100 << "\%\n";
    errs() <<"com:" << test1<<":"<<test2<<":"<<flagSC_opts<<":"<<costflagSC_opts<<"\n";
    return true;
}
bool StaPass::findSameSource(llvm::Instruction *BI1, llvm::Instruction *BI2, uint64_t id1, uint64_t id2, uint64_t flag) {
    // if (flag == 0) {
    //     if (getCheckType(BI2, SCI)) {
    //         return findAUSInst(BI1, BI2);
    //     }
        // else {
        //     return findSourceInst(BI1, BI2);
        // }
    // }
    // else if (flag == 1) {
    //     if (getCheckType(BI2, SCI)) {
    //         return findSourceInst(BI1, BI2);
    //     }
    //     else {
    //         return findSourceInst(BI1, BI2);
    //     }
    // }
    // else {
    //     return false;
    // }
    std::set<Value*> FClist1 = TrackMemoryLoc(BI1, id1);
    std::set<Value*> FClist2 = TrackMemoryLoc(BI2, id2);
    return SameMemoryLoc(FClist1, FClist2, id1, id2);
    // return false;
}

std::set<Value*> StaPass::TrackMemoryLoc(Instruction *C, uint64_t id) {
    std::set<Instruction*> Clist;
    std::set<Value*> FClist;
    bool flag = true;
    Instruction *Inst;
    if (BranchInst *BI = dyn_cast<BranchInst>(C)) {
        if (Instruction *Op=dyn_cast<Instruction>(C->getOperand(0))) {
            Clist.insert(Op);
        }
        else {
            flag = false;
        }
    }
    else {
        bool is_end = true;
        for (Use &U: C->operands()) {
            if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
                is_end = false;
            }
        }
        if (!is_end) {
            Clist.insert(C);
        }
        else {
            flag = false;
        }
    }

    StringRef OpName = C->getOpcodeName();
    while (Clist.size()!=0) {
        flag = false;
        Inst = *Clist.begin(); 
        Clist.erase(Inst);           
        OpName = Inst->getOpcodeName();
        if (id == 617 || id == 623) {
            errs() << "---" << id << ":" << OpName << "---";
        }
        bool is_end = true;
        for (Use &U: Inst->operands()) {
            if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
                is_end = false;
            }
        }
        if (OpName!="load" && !OpName.startswith("getelementptr") && OpName!="phi" && !is_end) {
            flag = true;
            for (Use &U: Inst->operands()) {
                if (Instruction *I = dyn_cast<Instruction>(U.get())) {
                    Clist.insert(I);
                }
                else if (Constant *C = dyn_cast<Constant>(U.get())) {
                    // Do nothing
                    // FClist.insert(U.get());
                }
                else {
                    FClist.insert(U.get());
                }
            }
        }
        else {
            FClist.insert(Inst);
        }
    }
    return FClist;
}

bool StaPass::SameMemoryLoc(std::set<Value*> FClist1, std::set<Value*> FClist2, uint64_t id1, uint64_t id2) {
    bool flag = false;
    if (FClist1.size() <= FClist2.size() && FClist1.size() > 0) {
        while (!FClist1.empty()) {
            flag = false;
            Value *FC = *FClist1.begin();
            FClist1.erase(FC);
            for (std::set<Value*>::iterator I=FClist2.begin(); I!=FClist2.end(); ++I) {
                if (FC == *I) {
                    // Find same Value in FClist2, exit FOR loop, flag = true
                    // Continue to compare next Value in FClist1 
                    flag = true;
                }
                else if (Instruction *Op1=dyn_cast<Instruction>(FC)) {
                    if (Instruction *Op2=dyn_cast<Instruction>(*I)) {
                        flag = true;
                        StringRef name1 = Op1->getOpcodeName();
                        StringRef name2 = Op2->getOpcodeName();
                        if (name1 == name2 && Op1->getNumOperands() == 0 && Op2->getNumOperands() == 0) {
                            flag = true;
                        }
                        else if (name1 == name2 && name1 == "phi") {
                            if (Op1 != Op2) {
                                flag = false;
                            }
                            else {
                                flag = true;
                            }
                        }
                        else if (name1 == name2 && name1 == "load" && Op1->getNumOperands() == Op2->getNumOperands()) {
                            if (Instruction *SubOp1 = dyn_cast<Instruction>(Op1->getOperand(0))) {
                                if (Instruction *SubOp2 = dyn_cast<Instruction>(Op2->getOperand(0))) {
                                    flag = findSameSource(SubOp1, SubOp2, id1 , id2, 1);
                                    // if (!flag) {
                                    //     break;
                                    // }
                                }
                                else {
                                    // std::set<Value*> SubFClist1 = TrackMemoryLoc(SubOp1, id1);
                                    // std::set<Value*> SubFClist2;
                                    // SubFClist2.insert(Op2);
                                    // flag = SameMemoryLoc(SubFClist1, SubFClist2, id1, id2);
                                    flag = false;
                                }
                            }
                            else if (Op1->getOperand(0) != Op2->getOperand(0)) {
                                flag = false;
                            }
                        }
                        else if (name1 == name2 && name1 == "getelementptr" && Op1->getNumOperands() == Op2->getNumOperands() && Op1->getNumOperands() > 0) {
                            for (size_t i=0; i<Op1->getNumOperands();i++) {
                                if (Instruction *SubOp1 = dyn_cast<Instruction>(Op1->getOperand(i))) {
                                    if (Instruction *SubOp2 = dyn_cast<Instruction>(Op2->getOperand(i))) {
                                        flag = findSameSource(SubOp1, SubOp2, 0 , 0, 1);
                                    }
                                    else {
                                        flag = false;
                                    }
                                }
                                else if (ConstantInt *V1 = dyn_cast<ConstantInt>(Op1->getOperand(i))) {
                                    if (ConstantInt *V2 = dyn_cast<ConstantInt>(Op2->getOperand(i))) {
                                        if (V1->getZExtValue() > V2->getZExtValue()) {
                                            flag = false;
                                        }
                                    }
                                }
                                else if (Op1->getOperand(i) != Op2->getOperand(i)) {
                                    flag = false;
                                }
                                if (!flag) {
                                    break;
                                }
                            }
                        }
                        else if (name1 == name2 && Op1->getNumOperands() == Op2->getNumOperands() && Op1->getNumOperands() > 0) {
                            
                            for (size_t i=0; i<Op1->getNumOperands();i++) {
                                if (Op1->getOperand(i) != Op2->getOperand(i)) {
                                    flag = false;
                                    break;
                                }
                            }
                        }
                        else {
                            flag = false;
                        }
                    }
                }
                if (flag) {
                    // Find same Value in FClist2, exit FOR loop, flag = true
                    // Continue to compare next Value in FClist1 
                    break;
                }
            }
            if (!flag) {
                // No same Value in FClist2, exit WHILE loop, flag = false
                break;
            }
        }
    }
    return flag;
}

// Tries to remove a sanity check; returns true if it worked.
void StaPass::optimizeCheckAway(Instruction *Inst) {
    BranchInst *BI = cast<BranchInst>(Inst);
    assert(BI->isConditional() && "Sanity check must be conditional branch.");
    
    unsigned int RegularBranch = getRegularBranch(BI, SCI);
    
    bool Changed = false;
    if (RegularBranch == 0) {
        BI->setCondition(ConstantInt::getTrue(Inst->getContext()));
        Changed = true;
    } else if (RegularBranch == 1) {
        BI->setCondition(ConstantInt::getFalse(Inst->getContext()));
        Changed = true;
    } else {
        dbgs() << "Warning: Sanity check with no regular branch found.\n";
        dbgs() << "The sanity check has been kept intact.\n";
    }
    // return Changed;
}

void StaPass::getAnalysisUsage(AnalysisUsage& AU) const {
    AU.addRequired<SCIPass>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.setPreservesAll();
}


char StaPass::ID = 0;
static RegisterPass<StaPass> X("StaPass",
        "Finds costs of sanity checks", false, false);



