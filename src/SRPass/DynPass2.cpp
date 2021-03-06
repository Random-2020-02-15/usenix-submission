// This file is part of ASAP.
// Please see LICENSE.txt for copyright and licensing information.

#include "DynPass2.h"
#include "SCIPass.h"
#include "utils.h"
#include "CostModel.h"
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
#define DEBUG_TYPE "dynpass2"

using namespace llvm;



static cl::opt<std::string>
InputSCOV("scov2", cl::desc("<input scov file>"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
InputUCOV("ucov2", cl::desc("<input ucov file>"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
InputLOG("log2", cl::desc("<input log file>"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
InputLOGG("logg2", cl::desc("<input log file>"), cl::init(""), cl::Hidden);


bool DynPass2::runOnModule(Module &m) {
    SCI = &getAnalysis<SCIPass>();
    TargetTransformInfoWrapperPass &TTIWP = getAnalysis<TargetTransformInfoWrapperPass>();
    std::string filename = m.getSourceFileName();
    filename = filename.substr(0, filename.rfind("."));
    

    struct tmp{
        uint64_t id;
        uint64_t count[3];
    }BrInfo;
    typedef uint64_t Info[3];
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
    int count = 0;
    // for (Function &F: m) {
    //     for (Instruction *Inst: SCI->getSCBranches(&F)) {
    //         optimizeCheckAway(Inst);

    //     }
    // }

    FILE *fp_sc = fopen(Twine(InputSCOV).str().c_str(), "rb");
    // errs() << Twine(InputSCOV).str().c_str() << "\n";
    // assert(fp_sc != NULL && "No valid SCOV file");
    FILE *fp_uc = fopen(Twine(InputUCOV).str().c_str(), "rb");
    // assert(fp_uc != NULL && "No valid UCOV file");
    if (fp_sc != NULL && fp_uc != NULL) {
    errs() << "DynPass2 on "<<filename << ";" << Twine(InputSCOV).str().c_str() << "\n";

    uint64_t flagSC = 0, costflagSC = 0; // Number of SCs
    uint64_t flagUC = 0, costflagUC = 0; // Number of UCs
    uint64_t flagSC_opt = 0, costflagSC_opt = 0; // Number of SCs after the redundant SCs about UCs are reduced
    uint64_t flagSC_opts = 0, costflagSC_opts = 0; // Number of SCs after the redundant SCs about SCs are reduced
    uint64_t test1 = 0, test2 = 0, test3 = 0;
    bool is_reduced = true;

    // Start reading and storing SC coverage records from InputSCOV
    for (Function &F: m) {
        for (Instruction *Inst: SCI->getSCBranches(&F)) {
            assert(Inst->getParent()->getParent() == &F && "SCI must only contain instructions of the current function.");
            BranchInst *BI = dyn_cast<BranchInst>(Inst);
            assert(BI && BI->isConditional() && "SCBranches must not contain instructions that aren't conditional branches.");
            fread(&BrInfo, sizeof(BrInfo), 1, fp_sc);
            // Revise the coverage pattern of SC
            // errs() <<"SC:"<<BrInfo.id << ":"<< BrInfo.count[0] <<":"<< BrInfo.count[1] <<":"<< BrInfo.count[2] << "\n";
            BrInfo.count[0] = BrInfo.count[1] + BrInfo.count[2];
            // Store the coverage data by UC_Stat
            // if (BrInfo.count[0] > 0) {
            //     optimizeCheckAway(Inst);
            // }
            // if (BrInfo.id >= 110 && BrInfo.id <= 110) {
            //     reducedSC[BrInfo.id] = 1;
            //     // optimizeCheckAway(Inst);
            // }
            
            for (size_t i=0;i<3;i++){
                SC_Stat[Inst][i] = BrInfo.count[i];
            }

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
        for (Instruction *Inst: SCI->getUCBranches(&F)) {
            assert(Inst->getParent()->getParent() == &F && "SCI must only contain instructions of the current function.");
            BranchInst *BI = dyn_cast<BranchInst>(Inst);
            assert(BI && BI->isConditional() && "UCBranches must not contain instructions that aren't conditional branches.");
            fread(&BrInfo, sizeof(BrInfo), 1, fp_uc);

            flagUC += 1;
            costflagUC += BrInfo.count[0];
            // For each instruction in UCBranch, check whether its coverage pattern matches certain patterns in SC_Pattern
            if (BrInfo.id == 37) {
                errs() << "UC 37:" << BrInfo.count[0] << ":" << BrInfo.count[1] << ":" << BrInfo.count[2] << "\n";
            }
            if (BrInfo.id >= 28 && BrInfo.id <= 37) {
                errs() << "UC:" << BrInfo.id << ":" << BrInfo.count[0] << ":" << BrInfo.count[1] << ":" << BrInfo.count[2] << "\n";
            }
            if (SC_Pattern.count(BrInfo.count[0]) > 0 && BrInfo.count[0] > 0) {
                // If UC and SC have ompletely the same dynamic pattern A+B:A:B
                for (stat Info: SC_Pattern[BrInfo.count[0]]) {
                    if ((Info.LB == BrInfo.count[1] && Info.RB == BrInfo.count[2]) || (Info.LB == BrInfo.count[2] && Info.RB == BrInfo.count[1])) {
                        // If UC and SC operate the same variable
                        // errs() << "TTT"<<Info.id << "---";
                        if (findPhiInst(Inst, Info.SC,BrInfo.id,Info.id) && reducedSC.count(Info.id) == 0) {
                            optimizeCheckAway(Info.SC);
                            errs() << "Reduced::UC:" << BrInfo.id<<"SC:"<<Info.id <<":"<< BrInfo.count[0]<<"--------\n";
                            flagSC_opt -= 1;
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
                        if (findPhiInst(Inst, Info.SC,BrInfo.id,Info.id) && reducedSC.count(Info.id) == 0) {
                            optimizeCheckAway(Info.SC);
                            errs() << "Reduced::UC:" << BrInfo.id<<"SC:"<<Info.id <<":"<< BrInfo.count[1]<<"--------\n";
                            flagSC_opt -= 1;
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
                        if (findPhiInst(Inst, Info.SC, BrInfo.id,Info.id) && reducedSC.count(Info.id) == 0) {
                            optimizeCheckAway(Info.SC);
                            errs() << "Reduced::UC:" << BrInfo.id<<"SC:"<<Info.id <<":"<< BrInfo.count[1]<< "--------\n";
                            flagSC_opt -= 1;
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
    uint64_t Cost = 0, Total_Cost = 0, Total_Cost_Opt = 0;
    for (Function &F: m) {
        const TargetTransformInfo &TTI = TTIWP.getTTI(F);
        for (Instruction *Inst: SCI->getSCBranches(&F)) {
            assert(Inst->getParent()->getParent() == &F && "SCI must only contain instructions of the current function.");
            BranchInst *BI = dyn_cast<BranchInst>(Inst);
            assert(BI && BI->isConditional() && "SCBranches must not contain instructions that aren't conditional branches.");
            fread(&BrInfo, sizeof(BrInfo), 1, fp_sc);
            // errs() <<"SC:"<<BrInfo.id << ":"<< BrInfo.count[0] <<":"<< BrInfo.count[1] <<":"<< BrInfo.count[2] << "\n";
            BrInfo.count[0] = BrInfo.count[1] + BrInfo.count[2];
            
            // Calculate cost of each checks
            Cost = 0;
            for (Instruction *CI: SCI->getInstructionsBySanityCheck(BI)) {
                unsigned CurrentCost = CheckCost::getInstructionCost(CI, &TTI);
                if (CurrentCost == (unsigned)(-1)) {
                    CurrentCost = 1;
                }
                Cost += CurrentCost * BrInfo.count[0];
            }
            Total_Cost += Cost;
            Total_Cost_Opt += Cost;
            tmp++;
            // Set a flag to record whether the SC can be reduced
            is_reduced = false;
            // For each instruction in SCBranch, check whether its dynamic pattern matches certain patterns in SC_Pattern_opt
            if (SC_Pattern.count(BrInfo.count[0]) > 0 && BrInfo.count[0] > 0) {
                // New SC and existing SC have ompletely the same dynamic pattern A+B:A:B
                // Check all SCs in SC_Pattern_opt
                for (stat Info: SC_Pattern[BrInfo.count[0]]) {
                    if (BrInfo.count[1] == Info.LB || BrInfo.count[2] == Info.LB) {
                        // Also the same operation variable 
                        // errs() << tmp << ":"<<Info.id << "---";

                        if (BrInfo.id != Info.id && findPhiInst(Info.SC, Inst, Info.id, BrInfo.id)) {
                            is_reduced = true;
                            if (reducedSC.count(BrInfo.id) == 0) {
                                optimizeCheckAway(Inst);
                                errs() << "Reduced::SC:" << BrInfo.id<<"SC:"<<Info.id <<":"<< BrInfo.count[0]<< "--------\n";
                                flagSC_opts -= 1;
                                costflagSC_opts -= BrInfo.count[0];
                                reducedSC[BrInfo.id] = BrInfo.count[0];
                            }
                        }
                    }
                }
            } 
            // Calculate reduced asap cost
            if (reducedSC.count(BrInfo.id) == 1) {
                Total_Cost_Opt -= Cost;
                test3 += 1;
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
                // SC_Pattern_opt[BrInfo.count[0]].push_back(SC_Info);
                if (reducedSC.count(BrInfo.id) == 0) {
                    test1 += 1;
                    test2 += BrInfo.count[0];
                }
            }
        }
    }
    fclose(fp_sc);
    errs() << "UC num :: " << flagUC << ";SC Num :: " << flagSC << ";SC percent after L1 :: " << flagSC_opt * 1.0 / (flagSC + 0.000000001) * 100 << "\%;SC percent after L2 :: " << flagSC_opts * 1.0 / (flagSC + 0.000000001) * 100 << "\%\n";
    errs() << "SC cost percent:: "<< costflagSC / (costflagSC + 0.000000001) * 100  << ";SC cost percent after L1 :: " << costflagSC_opt * 1.0 / (costflagSC + 0.000000001) * 100 << "\%;SC cost percent after L2 :: " << costflagSC_opts * 1.0 / (costflagSC + 0.000000001) * 100 << "\%\n";
    errs() <<"com:" << test1<<":"<<test2<<":"<<flagSC_opts<<":"<<costflagSC_opts<<"\n";
    errs() << "test:" << test3 << ":" << flagSC - flagSC_opts << "\n";
    errs() << "Total asap cost:" << Total_Cost << "Reduced total asap cost" << Total_Cost_Opt << "\n";
    // FILE *fp = fopen(Twine(InputLOG).str().c_str(), "rb");
    float data[6];
    // if (fp == NULL) {
    //     fp = fopen(Twine(InputLOG).str().c_str(), "wb");
    //     fprintf(fp, "%lu %lu %lu %lu %lu %lu\n",flagSC, flagSC_opt,flagSC_opts,costflagSC,costflagSC_opt,costflagSC_opts);
    //     fclose(fp);
    // }
    // else {
    //     fscanf(fp, "%lu %lu %lu %lu %lu %lu\n",&data[0],&data[1],&data[2],&data[3],&data[4],&data[5]);
    //     errs() << data[0] << ":" << data[1] << "\n";
    //     fp = fopen(Twine(InputLOG).str().c_str(), "wb");
    //     data[0] += flagSC;
    //     data[1] += flagSC_opt;
    //     data[2] += flagSC_opts;
    //     data[3] += costflagSC;
    //     data[4] += costflagSC_opts;
    //     fprintf(fp, "%lu %lu %lu %lu %lu %lu\n",flagSC, flagSC_opt,flagSC_opts,costflagSC,costflagSC_opt,costflagSC_opts);
    //     fclose(fp);
    // }
    FILE *fpp = fopen(Twine(InputLOGG).str().c_str(), "ab");
    fprintf(fpp, "%s %lu %lu %lu %lu %lu %lu %lu %lu\n", filename.c_str(), flagSC, flagSC_opt,flagSC_opts,costflagSC,costflagSC_opt,costflagSC_opts, Total_Cost, Total_Cost_Opt);
    fclose(fpp);
    }
    return true;
}

// bool DynPass2::findPhiInst(Instruction *UC_Inst, Instruction *SC_Inst, uint64_t id1, uint64_t id2) {
//     std::map<Instruction*,int> UC_list;
//     std::map<Value*,int> UC_Slist;
//     UC_list.insert(std::pair<Instruction*,int>(UC_Inst, 1));
//     std::map<Instruction*,int> SC_list;
//     std::map<Value*,int> SC_Slist;
//     SC_list.insert(std::pair<Instruction*,int>(SC_Inst, 1));
//     bool flag = true;
//     bool is_end = true;
//     uint64_t count = 0;
//     Instruction *Inst;
//     while (!SC_list.empty()) {
//         flag = false;
//         Instruction *Inst = SC_list.begin()->first;
//         SC_list.erase(Inst);
//         StringRef OpName = Inst->getOpcodeName();
//         if (OpName == "phi") {
//             if (SC_Slist.find(Inst) != SC_Slist.end()) {
//                 SC_Slist[Inst] += 1;
//             }
//             else {
//                 SC_Slist.insert(std::pair<Instruction*,int>(Inst,1));
//             }
//         }
//         else if (BranchInst *BI = dyn_cast<BranchInst>(Inst)) {
//             if (Instruction *Op=dyn_cast<Instruction>(Inst->getOperand(0))) {
//                 if (SC_list.find(Op) != SC_list.end()) {
//                     SC_list[Op] += 1;
//                 }
//                 else {
//                     SC_list.insert(std::pair<Instruction*,int>(Op,1));
//                 }
//             }
//         }
//         else {
//             flag = true;
//         }
//         if (flag) {
//             count = 0;
//             is_end = true;
//             for (Use &U: Inst->operands()) {
//                 if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
//                     if (SC_list.find(Op) != SC_list.end()) {
//                         SC_list[Op] += 1;
//                     }
//                     else {
//                         SC_list.insert(std::pair<Instruction*,int>(Op,1));
//                     }
//                     is_end = false;
//                 }
//                 else if (Constant *C = dyn_cast<Constant>(U.get())) {
//                     count += 1;
//                 }
//                 else {
//                     if (SC_Slist.find(U.get()) != SC_Slist.end()) {
//                         SC_Slist[U.get()] += 1;
//                     }
//                     else {
//                         SC_Slist.insert(std::pair<Value*,int>(U.get(),1));
//                     }
//                 }
//             }
//             if (count == Inst->getNumOperands()) {
//                 if (SC_Slist.find(Inst) != SC_Slist.end()) {
//                     SC_Slist[Inst] += 1;
//                 }
//                 else {
//                     SC_Slist.insert(std::pair<Instruction*,int>(Inst,1));
//                 }
//             }
//         }
//     }

//     flag = true;
//     while (!UC_list.empty()) {
//         flag = false;
//         Instruction *Inst = UC_list.begin()->first;
//         UC_list.erase(Inst);
//         StringRef OpName = Inst->getOpcodeName();
//         if (OpName == "phi") {
//             if (UC_Slist.find(Inst) != UC_Slist.end()) {
//                 UC_Slist[Inst] += 1;
//             }
//             else {
//                 UC_Slist.insert(std::pair<Instruction*,int>(Inst,1));
//             }
//         }
//         else if (BranchInst *BI = dyn_cast<BranchInst>(Inst)) {
//             if (Instruction *Op=dyn_cast<Instruction>(Inst->getOperand(0))) {
//                 if (UC_list.find(Op) != UC_list.end()) {
//                     UC_list[Op] += 1;
//                 }
//                 else {
//                     UC_list.insert(std::pair<Instruction*,int>(Op,1));
//                 }
//             }
//         }
//         else {
//             flag = true;
//         }

//         if (flag) {
//             count = 0;
//             is_end = true;
//             for (Use &U: Inst->operands()) {
//                 if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
//                     if (UC_list.find(Op) != UC_list.end()) {
//                         UC_list[Op] += 1;
//                     }
//                     else {
//                         UC_list.insert(std::pair<Instruction*,int>(Op,1));
//                     }
//                     is_end = false;
//                 }
//                 else if (Constant *C = dyn_cast<Constant>(U.get())) {
//                     count += 1;
//                 }
//                 else {
//                     if (UC_Slist.find(U.get()) != UC_Slist.end()) {
//                         UC_Slist[U.get()] += 1;
//                     }
//                     else {
//                         UC_Slist.insert(std::pair<Value*,int>(U.get(),1));
//                     }
//                 }
//             }
//             if (count == Inst->getNumOperands()) {
//                 if (UC_Slist.find(Inst) != UC_Slist.end()) {
//                     UC_Slist[Inst] += 1;
//                 }
//                 else {
//                     UC_Slist.insert(std::pair<Instruction*,int>(Inst,1));
//                 }
//             }
//         }
//     }
//     flag = false;
//     if (SC_Slist.size() == UC_Slist.size()) {
//         while (!SC_Slist.empty()) {
//             flag = false;
//             Value *SC_Inst = SC_Slist.begin()->first;
//             if (UC_Slist.find(SC_Inst) != UC_Slist.end()) {
//                 if (UC_Slist[SC_Inst] == SC_Slist[SC_Inst]) {
//                     flag = true;
//                 }
//             }
//             if (!flag) {
//                 break;
//             }
//             SC_Slist.erase(SC_Inst);
//         }
//     }
//     return flag;
// }


bool DynPass2::findPhiInst(Instruction *UC_Inst, Instruction *SC_Inst, uint64_t id1, uint64_t id2) {
    std::set<Instruction*> UC_list;
    std::set<Value*> UC_Slist;
    UC_list.insert(UC_Inst);
    std::set<Instruction*> SC_list;
    std::set<Value*> SC_Slist;
    SC_list.insert(SC_Inst);
    bool flag = true;
    bool is_end = true;
    uint64_t count = 0;
    Instruction *Inst;
    while (!SC_list.empty()) {
        flag = false;
        Instruction *Inst = *SC_list.begin();
        SC_list.erase(Inst);
        StringRef OpName = Inst->getOpcodeName();
        if (OpName == "phi") {
            SC_Slist.insert(Inst);
        }
        else if (BranchInst *BI = dyn_cast<BranchInst>(Inst)) {
            if (Instruction *Op=dyn_cast<Instruction>(Inst->getOperand(0))) {
                SC_list.insert(Op);
            }
        }
        else {
            flag = true;
        }
        if (flag) {
            if (id1 == 610 && id2 == 609) {
                errs() << "***" << OpName << ":" << SC_Slist.size() << ":" <<Inst->getNumOperands();
            }
            count = 0;
            is_end = true;
            for (Use &U: Inst->operands()) {
                if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
                    SC_list.insert(Op);
                    is_end = false;
                    if (id1 == 610 && id2 == 609) {
                        errs() << "Inst:";
                    }
                }
                else if (Constant *C = dyn_cast<Constant>(U.get())) {
                    if (id1 == 610 && id2 == 609) {
                        errs() << "Const:";
                    }
                    // SC_Slist.insert(C);
                    count += 1;
                    // if (OpName == "icmp") {
                    //     SC_Slist.insert(C);
                    // }
                }
                else {
                    if (id1 == 610 && id2 == 609) {
                        errs() << "Not Const:";
                    }
                    SC_Slist.insert(U.get());
                }
            }
            // if (Inst->getNumOperands() == 0) {
            //     SC_Slist.insert(Inst);
            // }
            if (count == Inst->getNumOperands()) {
                SC_Slist.insert(Inst);
            }
        }
    }
    if (id1 == 610 && id2 == 609) {
        errs() << "SSSSCCCC***" << SC_Slist.size();
    }
    flag = true;
    while (!UC_list.empty()) {
        flag = false;
        Instruction *Inst = *UC_list.begin();
        UC_list.erase(Inst);
        StringRef OpName = Inst->getOpcodeName();
        if (OpName == "phi") {
            UC_Slist.insert(Inst);
        }
        else if (BranchInst *BI = dyn_cast<BranchInst>(Inst)) {
            if (Instruction *Op=dyn_cast<Instruction>(Inst->getOperand(0))) {
                UC_list.insert(Op);
            }
        }
        else {
            flag = true;
        }

        if (flag) {
            if (id1==610 && id2 == 609) {
                errs() << "***" << OpName << ":" << UC_Slist.size() << ":" <<Inst->getNumOperands();
            }
            count = 0;
            is_end = true;
            for (Use &U: Inst->operands()) {
                if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
                    UC_list.insert(Op);
                    is_end = false;
                    if (id1 == 610 && id2 == 609) {
                        errs() << "Inst:";
                    }
                }
                else if (Constant *C = dyn_cast<Constant>(U.get())) {
                    if (id1 == 610 && id2 == 609) {
                        errs() << "Const:";
                    }
                    // if (OpName == "icmp") {
                    //     UC_Slist.insert(C);
                    // }
                    // UC_Slist.insert(C);
                    count += 1;
                }
                else {
                    UC_Slist.insert(U.get());
                    if (id1 == 610 && id2 == 609) {
                        errs() << "Not Const:";
                    }
                }
            }
            // if (Inst->getNumOperands() == 0) {
            //     UC_Slist.insert(Inst);
            //     errs() << "hhhhhhhhhhhhhhhhhhhhhhhh";
            // }
            if (count == Inst->getNumOperands()) {
                UC_Slist.insert(Inst);
            }
        }
    }
    if (id1 == 610 && id2 == 609) {
        errs() << "UUUUCCCC***" << UC_Slist.size();
    }
    flag = false;
    if (SC_Slist.size() == UC_Slist.size()) {
        while (!SC_Slist.empty()) {
            flag = false;
            Value *SC_Inst = *SC_Slist.begin();
            SC_Slist.erase(SC_Inst);
            if (UC_Slist.count(SC_Inst) > 0) {
                flag = true;
            }
            if (!flag) {
                break;
            }
        }
    }

    return flag;
}

// Tries to remove a sanity check; returns true if it worked.
void DynPass2::optimizeCheckAway(Instruction *Inst) {
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


void DynPass2::getAnalysisUsage(AnalysisUsage& AU) const {
    AU.addRequired<TargetTransformInfoWrapperPass>();
    AU.addRequired<SCIPass>();
    AU.setPreservesAll();
}


char DynPass2::ID = 0;
static RegisterPass<DynPass2> X("DynPass2",
        "Finds costs of sanity checks", false, false);



