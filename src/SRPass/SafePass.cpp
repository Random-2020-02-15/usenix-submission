// This file is part of ASAP.
// Please see LICENSE.txt for copyright and licensing information.

#include "SafePass.h"
#include "SCIPass.h"
#include "CostModel.h"
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
#include "llvm/Analysis/TargetTransformInfo.h"

#include <algorithm>
#include <memory>
#include <system_error>
#define DEBUG_TYPE "safepass"

using namespace llvm;


static cl::opt<std::string>
InputSCOV("safe-scov", cl::desc("<input scov file>"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
InputUCOV("safe-ucov", cl::desc("<input ucov file>"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
CheckType("san-type", cl::desc("<sanitizer type, choose asan or ubsan>"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
SanType("san-level", cl::desc("<sanitizer level, choose L0 or L1 or L2 or L3>"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
CheckID("checkcost-id", cl::desc("printCheckID"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
CheckFile("checkcost-file", cl::desc("printCheckFile"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
LogPath("checkcost-logpath", cl::desc("<input ucov file>"), cl::init(""), cl::Hidden);

namespace {
    bool largerCost(const SafePass::CheckCostPair &a,
                     const SafePass::CheckCostPair &b) {
        return a.second > b.second;
    }
}

bool SafePass::runOnModule(Module &m) {
    SCI = &getAnalysis<SCIPass>();
    TargetTransformInfoWrapperPass &TTIWP = getAnalysis<TargetTransformInfoWrapperPass>();
    std::string filename = m.getSourceFileName();
    filename = filename.substr(0, filename.rfind("."));
    const char *checkid = CheckID.c_str();

    struct brinfo{
        uint64_t id;
        uint64_t count[3];
    }BrInfo;

    struct info{
        double CostLevel1;
        double CostLevel2;
        double NumLevel1;
        double NumLevel2;
        uint64_t id;
        uint64_t count[3];
    };

    struct stat{
        uint64_t id;
        uint64_t LB;
        uint64_t RB;
        Instruction* SC;
    };

    struct coststat{
        double CostLevel1;
        double CostLevel2;
        double NumLevel1;
        double NumLevel2;
        Instruction* SC;
    };
    // for (Function &F: m) {
    //     for (Instruction *Inst: SCI->getSCBranches(&F)) {
    //         optimizeCheckAway(Inst);
    //     }
    // }
    std::map<Instruction*, info> SC_Stat;
    std::map<uint64_t, std::vector<stat>> SC_Pattern, SC_Pattern_opt;
    std::map<uint64_t, std::vector<coststat>> CostLevelRange;
    std::vector<Instruction*> RSC;
    StringRef SCType = CheckType;
    StringRef SCLevel = SanType;

    FILE *fp_sc = fopen(Twine(InputSCOV).str().c_str(), "rb");
    // errs() << Twine(InputSCOV).str().c_str() << "\n";
    // assert(fp_sc != NULL && "No valid SCOV file");
    FILE *fp_uc = fopen(Twine(InputUCOV).str().c_str(), "rb");
    FILE *fp_check = fopen(Twine(LogPath).str().c_str(), "ab");
    // assert(fp_uc != NULL && "No valid UCOV file");
    if (fp_sc != NULL && fp_uc != NULL && fp_check != NULL) {
        errs() << "SafePass jj on "<<filename << "\n";

        uint64_t flagSC = 0, costflagSC = 0; // Number of SCs
        uint64_t flagUC = 0, costflagUC = 0; // Number of UCs
        uint64_t flagSC_opt = 0, costflagSC_opt = 0; // Number of SCs after the redundant SCs about UCs are reduced
        uint64_t flagSC_opts = 0, costflagSC_opts = 0; // Number of SCs after the redundant SCs about SCs are reduced
        uint64_t test1 = 0, test2 = 0;
        uint64_t nInstructions = 0, nFreeInstructions = 0, total_cost = 0, total_num = 0;
        bool is_reduced = true;

        // Start reading and storing SC coverage records from InputSCOV
        for (Function &F: m) {
            const TargetTransformInfo &TTI = TTIWP.getTTI(F);
            for (Instruction *Inst: SCI->getSCBranches(&F)) {
                assert(Inst->getParent()->getParent() == &F && "SCI must only contain instructions of the current function.");

                BranchInst *BI = dyn_cast<BranchInst>(Inst);
                assert(BI && BI->isConditional() && "SCBranches must not contain instructions that aren't conditional branches.");

                fread(&BrInfo, sizeof(BrInfo), 1, fp_sc);
                // Revise the coverage pattern of SC
                // errs() <<"SC:"<<BrInfo.id << ":"<< BrInfo.count[0] <<":"<< BrInfo.count[1] <<":"<< BrInfo.count[2] << "\n";
                BrInfo.count[0] = BrInfo.count[1] + BrInfo.count[2];
                if (BrInfo.id >= 53 && BrInfo.id <= 69) {
                    errs() << BrInfo.id << "::" << BrInfo.count[0] << "---";
                    reducedSC[63] = BrInfo.count[0];
                }
                // if (BrInfo.count[0] > 0) {
                //     optimizeCheckAway(Inst);
                // }
                // Store the coverage data by UC_Stat
                for (size_t i=0;i<3;i++){
                    SC_Stat[Inst].count[i] = BrInfo.count[i];
                }
                SC_Stat[Inst].id = BrInfo.id;
                SC_Stat[Inst].CostLevel1 = 0;
                SC_Stat[Inst].CostLevel2 = 0;
                SC_Stat[Inst].NumLevel1 = 0;
                SC_Stat[Inst].NumLevel2 = 0;


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
                total_num += 1;
                
                uint64_t Cost = 0;
                // Calculate cost of each checks
                for (Instruction *CI: SCI->getInstructionsBySanityCheck(BI)) {
                    unsigned CurrentCost = CheckCost::getInstructionCost(CI, &TTI);
                    if (CurrentCost == (unsigned)(-1)) {
                        CurrentCost = 1;
                    }
                    if (CurrentCost == 0) {
                        nFreeInstructions += 1;
                    }
                    Cost += CurrentCost * BrInfo.count[0];
                    total_cost += CurrentCost * BrInfo.count[0];
                }
                // CheckCostVec.push_back(std::make_pair(BI, Cost));
                struct coststat SCCostInfo;
                SCCostInfo.CostLevel1 = 0;
                SCCostInfo.CostLevel2 = 0;
                SCCostInfo.NumLevel1 = 0;
                SCCostInfo.NumLevel2 = 0;
                SCCostInfo.SC = Inst;
                CostLevelRange[Cost].push_back(SCCostInfo);
            }
        }
        // std::sort(CheckCostVec.begin(), CheckCostVec.end(), largerCost);
        fclose(fp_sc);
        // Finish reading and storing SC coverage records from InputSCOV
        // Calculate the cost level of 
        double CostLevel1 = 0, CostLevel2 = 0, NumLevel1 = 0, NumLevel2 = 0;
        if (total_cost == 0) {
            total_cost = 1;
        }
        if (total_num == 0) {
            total_num = 1;
        }
        errs() << "Total cost:" << total_cost << " ,total num:" << total_num << "\n";
        for (std::map<uint64_t, std::vector<coststat>>::iterator I=CostLevelRange.begin(); I!=CostLevelRange.end(); ++I) {
            // errs() << I->first << "::" << I->second.size() << "---\n";
            CostLevel2 += I->first * I->second.size();
            NumLevel2 += I->second.size();

            for (uint64_t i=0; i<I->second.size(); i++) {
                
                I->second[i].CostLevel1 = CostLevel1 / total_cost;
                I->second[i].CostLevel2 = CostLevel2 / total_cost;
                I->second[i].NumLevel1 = NumLevel1 / total_num;
                I->second[i].NumLevel2 = NumLevel2 / total_num;
                SC_Stat[I->second[i].SC].CostLevel1 = CostLevel1 / total_cost;
                SC_Stat[I->second[i].SC].CostLevel2 = CostLevel2 / total_cost;
                SC_Stat[I->second[i].SC].NumLevel1 = NumLevel1 / total_cost;
                SC_Stat[I->second[i].SC].NumLevel2 = NumLevel2 / total_cost;
                if (SC_Stat[I->second[i].SC].id == atoi(checkid) && InputSCOV == CheckFile) {
                    fprintf(fp_check, \
                    "Total cost: %lu\nNumber of sanitizer checks: %lu\nNo. %lu in a total of %lu sanitizer check with cost %lu\nCost range: [%lf, %lf], Rank range: [%lf, %f]\n",
                    total_cost, total_num, i, I->second.size(), I->first, \
                    I->second[i].CostLevel1, I->second[i].CostLevel2, \
                    I->second[i].NumLevel1, I->second[i].NumLevel2);
                    errs() << "&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n";
                    errs() << i << "in" << I->second.size() << ":" << I->second[i].CostLevel1 << "::" << I->second[i].CostLevel2 << 
                    ":" << I->second[i].NumLevel1 << "::" << I->second[i].NumLevel2 << "----\n";
                    errs() << "&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n";
                }
            }
            CostLevel1 = CostLevel2;
            NumLevel1 = NumLevel2;
        }

        // Start reading and storing UC coverage records from InputUCOV
        // During this process, each UC will be compared with all SCs in SC_Pattern
        // For each SC in SC_Pattern, if its coverage pattern matches that of UC
        // And if the variable it operates is the same as that operated by UC
        // Then, the SC can be reduced.
        flagSC_opt = flagSC;
        costflagSC_opt = costflagSC;
        errs() <<flagSC <<":"<<costflagSC << "----\n";
        for (Function &F: m) {
            for (Instruction *Inst: SCI->getUCBranches(&F)) {
                assert(Inst->getParent()->getParent() == &F && "SCI must only contain instructions of the current function.");
                BranchInst *BI = dyn_cast<BranchInst>(Inst);
                assert(BI && BI->isConditional() && "UCBranches must not contain instructions that aren't conditional branches.");
                fread(&BrInfo, sizeof(BrInfo), 1, fp_uc);
                // errs() <<"UC:"<<BrInfo.id << ":"<< BrInfo.count[0] <<":"<< BrInfo.count[1] <<":"<< BrInfo.count[2] << "\n";

                flagUC += 1;
                costflagUC += BrInfo.count[0];
                // For each instruction in UCBranch, check whether its coverage pattern matches certain patterns in SC_Pattern
                
                if (SC_Pattern.count(BrInfo.count[0]) > 0 && BrInfo.count[0] > 0) {
                    // If UC and SC have ompletely the same dynamic pattern A+B:A:B
                    for (stat Info: SC_Pattern[BrInfo.count[0]]) {
                        if ((Info.LB == BrInfo.count[1] && Info.RB == BrInfo.count[2]) || (Info.LB == BrInfo.count[2] && Info.RB == BrInfo.count[1])) {
                            // If UC and SC operate the same variable
                            // errs() << "TTT"<<Info.id << "---";
                            if (findSameSource(Info.SC, Inst, BrInfo.id, Info.id, 0, SCType, SCLevel)  && reducedSC.count(Info.id) == 0) {
                                optimizeCheckAway(Info.SC);
                                // errs() << "Reduced::UC:" << BrInfo.id<<"SC:"<<Info.id <<":"<< BrInfo.count[0]<<"--------\n";
                                if (Info.id == atoi(checkid) && InputSCOV == CheckFile) {
                                    fprintf(fp_check, "This check is redundant with user defined checks.\n");
                                }
                                flagSC_opt -= 1;
                                RSC.push_back(Info.SC);
                                costflagSC_opt -= BrInfo.count[0];
                                reducedSC[Info.id] = BrInfo.count[0];
                            }
                        }
                    }
                    if (SCLevel != "L0") {
                        for (stat Info: SC_Pattern[BrInfo.count[0]]) {
                            if (findPhiInst(Info.SC, Inst) && reducedSC.count(Info.id) == 0) {
                                optimizeCheckAway(Info.SC);
                                if (Info.id == atoi(checkid) && InputSCOV == CheckFile) {
                                    fprintf(fp_check, "This check is redundant with user defined checks.\n");
                                }
                                flagSC_opt -= 1;
                                RSC.push_back(Info.SC);
                                costflagSC_opt -= BrInfo.count[0];
                                reducedSC[Info.id] = BrInfo.count[0];
                            }
                        }
                    }
                }
                else if (SC_Pattern.count(BrInfo.count[1]) > 0 && BrInfo.count[1] > 0) {
                    // UC has pattern A+B:A:B, while SC has pattern A:A:0
                    for (stat Info: SC_Pattern[BrInfo.count[1]]) {
                        if (Info.LB == 0 || Info.RB == 0) {
                            // If UC and SC operate the same variable
                            if (findSameSource(Info.SC, Inst, BrInfo.id, Info.id, 0, SCType, SCLevel) && reducedSC.count(Info.id) == 0) {
                                optimizeCheckAway(Info.SC);
                                // errs() << "Reduced::UC:" << BrInfo.id<<"SC:"<<Info.id <<":"<< BrInfo.count[1]<<"--------\n";
                                if (Info.id == atoi(checkid) && InputSCOV == CheckFile) {
                                    fprintf(fp_check, "This check is redundant with user defined checks.\n");
                                }
                                flagSC_opt -= 1;
                                RSC.push_back(Info.SC);
                                costflagSC_opt -= BrInfo.count[1];
                                reducedSC[Info.id] = BrInfo.count[1];
                            }
                        }
                    }
                }
                else if (SC_Pattern.count(BrInfo.count[2]) > 0 && BrInfo.count[2] > 0) {
                    // UC has pattern A+B:A:B, while SC has pattern B:B:0
                    for (stat Info: SC_Pattern[BrInfo.count[2]]) {
                        if (Info.LB == 0 || Info.RB == 0){
                            if (findSameSource(Info.SC, Inst, BrInfo.id, Info.id, 0, SCType, SCLevel) && reducedSC.count(Info.id) == 0) {
                                optimizeCheckAway(Info.SC);
                                // errs() << "Reduced::UC:" << BrInfo.id<<"SC:"<<Info.id <<":"<< BrInfo.count[1]<< "--------\n";
                                if (Info.id == atoi(checkid) && InputSCOV == CheckFile) {
                                    fprintf(fp_check, "This check is redundant with user defined checks.\n");
                                }
                                flagSC_opt -= 1;
                                RSC.push_back(Info.SC);
                                costflagSC_opt -= BrInfo.count[2];
                                reducedSC[Info.id] = BrInfo.count[2];
                            }
                        }
                    }
                }
            }
        }
        fclose(fp_uc);
        // Finish reading and storing UC coverage records from InputUCOV

        // Reduce redundant SCs among SCs
        // For each SC read from SCOV file
        // Check whether its pattern matches any SCs in SC_Pattern_opt
        // If it is, this SC can be reduced
        flagSC_opts = flagSC_opt;
        costflagSC_opts = costflagSC_opt;
        errs() <<flagSC_opt <<":"<<costflagSC_opt << "----\n";
        fp_sc = fopen(Twine(InputSCOV).str().c_str(), "rb");
        uint64_t tmp = 0;
        for (Function &F: m) {
            for (Instruction *Inst: SCI->getSCBranches(&F)) {
                assert(Inst->getParent()->getParent() == &F && "SCI must only contain instructions of the current function.");
                BranchInst *BI = dyn_cast<BranchInst>(Inst);
                assert(BI && BI->isConditional() && "SCBranches must not contain instructions that aren't conditional branches.");
                fread(&BrInfo, sizeof(BrInfo), 1, fp_sc);
                // errs() <<"SC:"<<BrInfo.id << ":"<< BrInfo.count[0] <<":"<< BrInfo.count[1] <<":"<< BrInfo.count[2] << "\n";
                // fprintf(fp,"SC:%lu:%lu:%lu:%lu\n",BrInfo.id, BrInfo.count[0], BrInfo.count[1], BrInfo.count[2]);
                BrInfo.count[0] = BrInfo.count[1] + BrInfo.count[2];
                tmp++;
                // Set a flag to record whether the SC can be reduced
                is_reduced = false;
                // For each instruction in SCBranch, check whether its dynamic pattern matches certain patterns in SC_Pattern_opt
                if (SC_Pattern_opt.count(BrInfo.count[0]) > 0 && BrInfo.count[0] > 0) {
                    // New SC and existing SC have ompletely the same dynamic pattern A+B:A:B
                    // Check all SCs in SC_Pattern_opt
                    for (stat Info: SC_Pattern_opt[BrInfo.count[0]]) {
                        if (BrInfo.count[1] == Info.LB || BrInfo.count[2] == Info.LB) {
                            // Also the same operation variable 
                            // errs() << tmp << ":"<<Info.id << "---";
                            if (findSameSource(Inst, Info.SC, BrInfo.id, Info.id, 1, SCType, SCLevel)) {
                                is_reduced = true;
                                // errs() << "Same::SC:" << SC_Stat[Inst].id<<"SC:"<<SC_Stat[Info.SC].id << ":"<<SC_Stat[Inst].CostLevel1<<"-"<<SC_Stat[Inst].CostLevel2<<"---\n";
                                if (reducedSC.count(BrInfo.id) == 0) {
                                    optimizeCheckAway(Inst);
                                    if (BrInfo.id == atoi(checkid) && InputSCOV == CheckFile) {
                                        fprintf(fp_check, "This check is redundant with sanitizer checks.\n");
                                    }
                                    flagSC_opts -= 1;
                                    RSC.push_back(Inst);
                                    costflagSC_opts -= BrInfo.count[0];
                                    reducedSC[BrInfo.id] = BrInfo.count[0];
                                }
                            }
                        }
                    }
                }
                // If the SC cannot be reduced, it should be inserted into SC_Pattern_opt, becoming one of the existing SCs.
                if (!is_reduced) {
                    // Insert this Instruction into SC_Pattern_opt
                    // Including its id, LB, RB, and *Inst
                    struct stat SC_Info;
                    SC_Info.id = BrInfo.id;
                    SC_Info.LB = BrInfo.count[1];
                    SC_Info.RB = BrInfo.count[2];
                    SC_Info.SC = Inst;
                    SC_Pattern_opt[BrInfo.count[0]].push_back(SC_Info);
                    if (reducedSC.count(BrInfo.id) == 0) {
                        test1 += 1;
                        test2 += BrInfo.count[0];
                    }
                }
            }
        }
        fclose(fp_sc);
        fclose(fp_check);
        errs() << "UC num :: " << flagUC << ";SC Num :: " << flagSC << ";SC percent after L1 :: " << flagSC_opt * 1.0 / flagSC * 100 << "\%;SC percent after L2 :: " << flagSC_opts * 1.0 / flagSC * 100 << "\%\n";
        // errs() << "SC cost percent:: "<< costflagSC/costflagSC * 100  << ";SC cost percent after L1 :: " << costflagSC_opt * 1.0 / costflagSC * 100 << "\%;SC cost percent after L2 :: " << costflagSC_opts * 1.0 / costflagSC * 100 << "\%\n";
        errs() <<"com:" << test1<<":"<<test2<<":"<<flagSC_opts<<":"<<costflagSC_opts<<"\n";
    }
    return true;
}
bool SafePass::findSameSource(Instruction *BI1, Instruction *BI2, uint64_t id1, uint64_t id2, size_t flag, StringRef SCType, StringRef SCLevel) {
    return true;
    if (SCLevel == "L3") {
        return true;
    }
    else if (flag == 0) {
        std::set<Instruction*> Clist1 = TrackMemoryLoc(BI1, SCType, id1, SCLevel);
        if (SCType == "asan" && SCLevel != "L0") {
            Clist1 = TrackMemoryLoc(BI1, SCType, id1, "L");
        }
        std::set<Instruction*> Clist2 = TrackMemoryLoc(BI2, "uc", id2, SCLevel);
        return SameMemoryLoc(Clist1, Clist2, SCLevel);
    }
    else if (flag == 1) {
        std::set<Instruction*> Clist1 = TrackMemoryLoc(BI1, SCType, id1, SCLevel);
        std::set<Instruction*> Clist2 = TrackMemoryLoc(BI2, SCType, id2, SCLevel);
        return SameMemoryLoc(Clist1, Clist2, SCLevel);
    }
    else {
        return false;
    }
}
bool SafePass::SameStaticPattern(Instruction *C1, Instruction *C2) {
    bool flag = false;
    StringRef name1 = C1->getOpcodeName();
    StringRef name2 = C2->getOpcodeName();
    if (C1 == C2) {
        return true;
    }
    else if (name1 == name2 && name1 !="phi" && C1->getNumOperands() == C2->getNumOperands() && C1->getNumOperands() != 0) {
        flag = true;
        for (size_t i=0; i<C1->getNumOperands();i++) {
            if (C1->getOperand(i) != C2->getOperand(i)) {
                flag = false;
                if (Instruction *Op1 = dyn_cast<Instruction>(C1->getOperand(i))) {
                    if (Instruction *Op2 = dyn_cast<Instruction>(C2->getOperand(i))) {
                        flag = SameStaticPattern(Op1, Op2);
                    }
                }
                if (!flag) {
                    break;
                }
            }
        }
        return flag;
    }
    return flag;
}

std::set<llvm::Instruction*> SafePass::TrackMemoryLoc(Instruction *C, StringRef type, uint64_t id, StringRef SCLevel) {
    std::set<Instruction*> Clist;
    bool flag = true;
    Instruction *Inst;
    if (SCLevel == "L0" || SCLevel == "L1") {
        if (Instruction *Op = dyn_cast<Instruction>(C->getOperand(0))) {
            Clist.insert(Op);
        }
        else {
            Clist.insert(C);
        }
        return Clist;
    }
    else if (type == "asan") {
        Clist.insert(C);
        while (flag) {
            flag = false;
            for (Instruction *I: Clist) {
                StringRef OpName = I->getOpcodeName();
                bool is_end = true;
                for (Use &U: I->operands()) {
                    if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
                        is_end = false;
                    }
                }
                if (!OpName.startswith("getelementptr") && OpName!="phi" && !is_end) {
                    flag = true;
                    Inst = I;
                    break;
                }
            }
            if (flag) {
                Clist.erase(Inst);
                for (Use &U: Inst->operands()) {
                    if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
                        Clist.insert(Op);
                    }
                }
            }
        }
        if (SCLevel == "L" && Clist.size() == 1) {
            Instruction *I = *Clist.begin();
            StringRef OpName = I->getOpcodeName();
            Clist.erase(I);
            if (OpName.startswith("getelementptr")) {
                for (size_t i=1; i<I->getNumOperands();i++) {
                    if (Instruction *Op = dyn_cast<Instruction>(I->getOperand(i))) {
                        std::set<Instruction*> SubClist = TrackMemoryLoc(Op, "uc", 0, SCLevel);
                        for (std::set<Instruction*>::iterator SI=SubClist.begin(); SI!=SubClist.end(); ++SI) {
                            Clist.insert(*SI);
                        }
                    }
                }
            }
            if (Clist.size() == 0) {
                Clist.insert(I);
            }

        }

        return Clist;
    }
    else if (type == "ubsan" || type == "uc") {
        Clist.insert(C);
        while (flag) {
            flag = false;
            for (Instruction *I: Clist) {
                StringRef OpName = I->getOpcodeName();
                bool is_end = true;
                for (Use &U: I->operands()) {
                    if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
                        is_end = false;
                    }
                }
                if (OpName!="phi" && !is_end) {
                    flag = true;
                    Inst = I;
                    break;
                }
            }
            if (flag) {
                Clist.erase(Inst);
                for (Use &U: Inst->operands()) {
                    if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
                        Clist.insert(Op);
                    }
                }
            }
        }
        return Clist;
    }
    return Clist;
}

bool SafePass::SameMemoryLoc(std::set<Instruction*> Clist1, std::set<Instruction*> Clist2, StringRef SCLevel) {
    bool flag = false;
    if (SCLevel == "L0" || SCLevel == "L1") {
        return SameStaticPattern(*Clist1.begin(), *Clist2.begin());
    }
    else if (SCLevel == "L2") {
        if (Clist1.size() <= Clist2.size() && Clist1.size() > 0) {
            while (!Clist1.empty()) {
                Instruction *C = *Clist1.begin();
                Clist1.erase(C);
                flag = false;
                for (std::set<Instruction*>::iterator I=Clist2.begin(); I!=Clist2.end(); ++I) {
                    StringRef name1 = C->getOpcodeName();
                    StringRef name2 = (*I)->getOpcodeName();
                    if (false && SameStaticPattern(C, *I)) {
                        flag = true;
                        break;
                    }
                    else if (name1.startswith("getelementptr") && name2.startswith("getelementptr") && C->getNumOperands() == (*I)->getNumOperands()) {
                        flag = true;
                        for (size_t i=0; i<C->getNumOperands();i++) {
                            if (Instruction *Op1 = dyn_cast<Instruction>(C->getOperand(i))) {
                                if (Instruction *Op2 = dyn_cast<Instruction>((*I)->getOperand(i))) {
                                    std::set<Instruction*> SubClist1 = TrackMemoryLoc(Op1, "uc", 0, "L2");
                                    std::set<Instruction*> SubClist2 = TrackMemoryLoc(Op2, "uc", 0, "L2");
                                    flag = SameMemoryLoc(SubClist1, SubClist2, SCLevel);
                                    if (!flag) {
                                        break;
                                    }
                                }
                            }
                            else if (ConstantInt *V1 = dyn_cast<ConstantInt>(C->getOperand(i))) {
                                if (ConstantInt *V2 = dyn_cast<ConstantInt>((*I)->getOperand(i))) {
                                    if (V1->getZExtValue() > V2->getZExtValue()) {
                                        flag = false;
                                        break;
                                    }
                                }
                            }
                            else if (C->getOperand(i) != (*I)->getOperand(i)) {
                                flag = false;
                                break;
                            }
                        }
                    }
                    if (flag) {
                        break;
                    }
                }
                if (!flag) {
                    break;
                }
            }
        }
        return flag;
    }
}



// Tries to remove a sanity check; returns true if it worked.
void SafePass::optimizeCheckAway(Instruction *Inst) {
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



void SafePass::getAnalysisUsage(AnalysisUsage& AU) const {
    AU.addRequired<TargetTransformInfoWrapperPass>();
    AU.addRequired<SCIPass>();
    AU.setPreservesAll();
}

bool SafePass::findPhiInst(Instruction *SC_Inst, Instruction *UC_Inst) {
    std::set<Instruction*> SC_list, UC_list;
    SC_list.insert(SC_Inst);
    UC_list.insert(UC_Inst);
    bool flag = true;
    Instruction *Inst;
    while (flag) {
        flag = false;
        for (Instruction *I: SC_list) {
            StringRef OpName = I->getOpcodeName();
            if (OpName!="phi") {
                flag = true;
                Inst = I;
                break;
            }
        }
        if (flag) {
            SC_list.erase(Inst);
            for (Use &U: Inst->operands()) {
                if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
                    SC_list.insert(Op);
                }
            }
        }
    }
    flag = true;
    while (flag) {
        flag = false;
        for (Instruction *I: UC_list) {
            StringRef OpName = I->getOpcodeName();
            if (OpName!="phi") {
                flag = true;
                Inst = I;
                break;
            }
        }
        if (flag) {
            UC_list.erase(Inst);
            for (Use &U: Inst->operands()) {
                if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
                    UC_list.insert(Op);
                }
            }
        }
    }
    flag = false;
    if (SC_list.size() == 1) {
        Instruction *SC = *SC_list.begin();
        StringRef Name = SC->getName();
        if (Name.startswith("indvars")) {
            flag = true;
        }
    }
    // else if (SC_list.size() == 1 && UC_list.size() == 1) {
    //     Instruction *SC = *SC_list.begin();
    //     Instruction *UC = *UC_list.begin();
    //     if (SC == UC) {
    //         flag = true;
    //     }
    // }
    return flag;
}

char SafePass::ID = 0;
static RegisterPass<SafePass> X("SafePass",
        "Finds costs of sanity checks", false, false);

