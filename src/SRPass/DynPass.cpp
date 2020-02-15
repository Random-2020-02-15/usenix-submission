// This file is part of ASAP.
// Please see LICENSE.txt for copyright and licensing information.

#include "DynPass.h"
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

#include <algorithm>
#include <memory>
#include <system_error>
#define DEBUG_TYPE "dynpass"

using namespace llvm;



static cl::opt<std::string>
InputSCOV("scov", cl::desc("<input scov file>"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
InputUCOV("ucov", cl::desc("<input ucov file>"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
InputLOG("log", cl::desc("<input log file>"), cl::init(""), cl::Hidden);

static cl::opt<std::string>
InputLOGG("logg", cl::desc("<input log file>"), cl::init(""), cl::Hidden);


bool DynPass::runOnModule(Module &m) {
    SCI = &getAnalysis<SCIPass>();
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
    errs() << "DynPass on "<<filename << ";" << Twine(InputSCOV).str().c_str() << "\n";

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
            fread(&BrInfo, sizeof(BrInfo), 1, fp_sc);
            // Revise the coverage pattern of SC
            // errs() <<"SC:"<<BrInfo.id << ":"<< BrInfo.count[0] <<":"<< BrInfo.count[1] <<":"<< BrInfo.count[2] << "\n";
            BrInfo.count[0] = BrInfo.count[1] + BrInfo.count[2];
            // Store the coverage data by UC_Stat
            // if (BrInfo.count[0] > 0) {
            //     optimizeCheckAway(Inst);
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

            if (SC_Pattern.count(BrInfo.count[0]) > 0 && BrInfo.count[0] > 0) {
                // If UC and SC have ompletely the same dynamic pattern A+B:A:B
                for (stat Info: SC_Pattern[BrInfo.count[0]]) {
                    if (findPhiInst(Inst, Info.SC)  && reducedSC.count(Info.id) == 0 && false) {
                        optimizeCheckAway(Info.SC);
                        errs() << "Reduced::UC:" << BrInfo.id<<"SC:"<<Info.id <<":"<< BrInfo.count[0]<<"--------\n";
                        flagSC_opt -= 1;
                        costflagSC_opt -= BrInfo.count[0];
                        reducedSC[Info.id] = BrInfo.count[0];
                    }
                    else if ((Info.LB == BrInfo.count[1] && Info.RB == BrInfo.count[2]) || (Info.LB == BrInfo.count[2] && Info.RB == BrInfo.count[1])) {
                        // If UC and SC operate the same variable
                        // errs() << "TTT"<<Info.id << "---";

                        if (findSameSourceS(Info.SC, Inst, BrInfo.id, Info.id, 0)  && reducedSC.count(Info.id) == 0) {
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
                        if (findSameSourceS(Info.SC, Inst, BrInfo.id, Info.id, 0) && reducedSC.count(Info.id) == 0) {
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
                        if (findSameSourceS(Info.SC, Inst, BrInfo.id, Info.id, 0) && reducedSC.count(Info.id) == 0) {
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
    for (Function &F: m) {
        for (Instruction *Inst: SCI->getSCBranches(&F)) {
            assert(Inst->getParent()->getParent() == &F && "SCI must only contain instructions of the current function.");
            BranchInst *BI = dyn_cast<BranchInst>(Inst);
            assert(BI && BI->isConditional() && "SCBranches must not contain instructions that aren't conditional branches.");
            fread(&BrInfo, sizeof(BrInfo), 1, fp_sc);
            // errs() <<"SC:"<<BrInfo.id << ":"<< BrInfo.count[0] <<":"<< BrInfo.count[1] <<":"<< BrInfo.count[2] << "\n";

            BrInfo.count[0] = BrInfo.count[1] + BrInfo.count[2];
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

                        if (BrInfo.id != Info.id && findSameSourceS(Inst, Info.SC, BrInfo.id, Info.id, 1)) {
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
    fprintf(fpp, "%s %lu %lu %lu %lu %lu %lu\n", filename.c_str(), flagSC, flagSC_opt,flagSC_opts,costflagSC,costflagSC_opt,costflagSC_opts);
    fclose(fpp);
    }
    return true;
}

bool DynPass::findSameSourceS(Instruction *B1, Instruction *B2, uint64_t id1, uint64_t id2, uint64_t f) {
    bool flag = false;
    Instruction* C1;
    Instruction* C2;
    StringRef name1 = B1->getOpcodeName();
    StringRef name2 = B2->getOpcodeName();
    if (name1 == "br" && name2 == "br") {
        if (Instruction *Op1 = dyn_cast<Instruction>(B1->getOperand(0))){
            if (Instruction *Op2 = dyn_cast<Instruction>(B2->getOperand(0))){
                C1 = Op1;
                C2 = Op2;
                name1 = C1->getOpcodeName();
                name2 = C2->getOpcodeName();
            }
            else {
                return false;
            }
        }
        else{
            return false;
        }
    }
    else {
        C1 = B1;
        C2 = B2;
        name1 = C1->getOpcodeName();
        name2 = C2->getOpcodeName();
    }
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
                        flag = findSameSourceS(Op1, Op2, id1, id2, f);
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

bool DynPass::findSameSource(llvm::Instruction *BI1, llvm::Instruction *BI2, uint64_t id1, uint64_t id2, uint64_t flag) {
    std::set<Value*> FClist1 = TrackMemoryLoc(BI1, id1);
    std::set<Value*> FClist2 = TrackMemoryLoc(BI2, id2);
    return SameMemoryLoc(FClist1, FClist2, id1, id2);
}

std::set<Value*> DynPass::TrackMemoryLoc(Instruction *C, uint64_t id) {
    std::set<Instruction*> Clist;
    std::set<Value*> FClist;
    Instruction *Inst;
    if (BranchInst *BI = dyn_cast<BranchInst>(C)) {
        if (Instruction *Op=dyn_cast<Instruction>(C->getOperand(0))) {
            Clist.insert(Op);
        }
    }
    else {
        bool is_end = true;
        for (Use &U: C->operands()) {
            if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
                is_end = false;
            }
        }
        StringRef OpName = C->getOpcodeName();
        if (!is_end) {
            Clist.insert(C);
        }
        // Clist.insert(C);
    }

    StringRef OpName = C->getOpcodeName();
    while (Clist.size()!=0) {
        Inst = *Clist.begin(); 
        Clist.erase(Inst);           
        OpName = Inst->getOpcodeName();
        bool is_end = true;
        for (Use &U: Inst->operands()) {
            if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
                is_end = false;
            }
        }
        // if (is_end && OpName != "load" && !OpName.startswith("getelementptr")) {
        //     errs() <<"id:" << id << "Opname:" << OpName << "\n";
        // }
        if (OpName!="load" && !OpName.startswith("getelementptr") && OpName!="phi" && !is_end) {
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

bool DynPass::SameMemoryLoc(std::set<Value*> FClist1, std::set<Value*> FClist2, uint64_t id1, uint64_t id2) {
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
                    break;
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
                        else if (name1 == name2 && name1 == "load") {
                            if (Instruction *SubOp1 = dyn_cast<Instruction>(Op1->getOperand(0))) {
                                if (Instruction *SubOp2 = dyn_cast<Instruction>(Op2->getOperand(0))) {
                                    flag = findSameSource(SubOp1, SubOp2, id1 , id2, 1);
                                }
                                else {
                                    flag = false;
                                }
                            }
                            else {
                                if (Instruction *SubOp2 = dyn_cast<Instruction>(Op2->getOperand(0))) {
                                    flag = findSameSource(Op1, SubOp2, id1 , id2, 1);
                                    if (flag) {
                                        errs() << "hhh";
                                    }
                                }
                                else if (Op1->getOperand(0) == Op2->getOperand(0)) {
                                    flag = true;
                                }
                                else {
                                    flag = false;
                                }
                            }
                        }
                        else if (name1.startswith("getelementptr") && name2.startswith("getelementptr") && Op1->getNumOperands() == Op2->getNumOperands()) {
                            for (size_t i=0; i<Op1->getNumOperands(); i++) {
                                if (Instruction *SubOp1 = dyn_cast<Instruction>(Op1->getOperand(i))) {
                                    if (Instruction *SubOp2 = dyn_cast<Instruction>(Op2->getOperand(i))) {
                                        flag = findSameSource(SubOp1, SubOp2, 0 , 0, 1);
                                        if (!flag) {
                                            break;
                                        }
                                    }
                                    else {
                                        flag = false;
                                        break;
                                    }
                                }
                                else if (ConstantInt *V1 = dyn_cast<ConstantInt>(Op1->getOperand(i))) {
                                    if (ConstantInt *V2 = dyn_cast<ConstantInt>(Op2->getOperand(i))) {
                                        if (V1->getZExtValue() > V2->getZExtValue()) {
                                            flag = false;
                                            break;
                                        }
                                        else {
                                            flag = true;
                                        }
                                    }
                                    else {
                                        flag = false;
                                        break;
                                    }
                                }
                                else if (Op1->getOperand(i) == Op2->getOperand(i)) {
                                    flag = true;
                                }
                                else {
                                    flag = true;
                                    if (Instruction *SubOp2 = dyn_cast<Instruction>(Op2->getOperand(i))) {
                                        std::set<Value*> SubFClist1;
                                        SubFClist1.insert(Op1->getOperand(i));
                                        std::set<Value*> SubFClist2 = TrackMemoryLoc(SubOp2, id2);
                                        if (SubFClist2.count(Op1->getOperand(i)) == 0) {
                                            flag = false;
                                            break;
                                        }
                                    }
                                    else {
                                        flag = false;
                                        break;
                                    }
                                }
                            }
                        }
                        else if (name1 == name2 && Op1->getNumOperands() == Op2->getNumOperands()) {
                            flag = true;
                            for (size_t i=0; i<Op1->getNumOperands();i++) {
                                if (Op1->getOperand(i) != Op2->getOperand(i)) {
                                    flag = false;
                                    break;
                                }
                            }
                        }
                        else if (Op2->getNumOperands() > 0 && name2 != "phi" ) {
                            flag = false;
                            for (size_t i=0; i<Op2->getNumOperands();i++){
                                if (Instruction *SubOp2 = dyn_cast<Instruction>(Op2->getOperand(i))) {
                                    flag = findSameSource(Op1, SubOp2, id1 , id2, 1);
                                }
                                if (flag) {
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


bool DynPass::findPhiInst(Instruction *UC_Inst, Instruction *SC_Inst) {
    std::set<Instruction*> UC_list;
    UC_list.insert(UC_Inst);
    std::set<Instruction*> SC_list;
    SC_list.insert(SC_Inst);
    bool flag = true;
    Instruction *Inst;
    while (flag && !SC_list.empty()) {
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
    // flag = true;
    // while (flag) {
    //     flag = false;
    //     for (Instruction *I: UC_list) {
    //         StringRef OpName = I->getOpcodeName();
    //         if (OpName!="phi") {
    //             flag = true;
    //             Inst = I;
    //             break;
    //         }
    //     }
    //     if (flag) {
    //         UC_list.erase(Inst);
    //         for (Use &U: Inst->operands()) {
    //             if (Instruction *Op = dyn_cast<Instruction>(U.get())) {
    //                 UC_list.insert(Op);
    //             }
    //         }
    //     }
    // }
    flag = false;
    if (SC_list.size() == 1) {
        Instruction *SC_Inst = *SC_list.begin();
        StringRef Name = SC_Inst->getName();
        if (Name.startswith("indvars")) {
            flag = true;
        }
    }
    // if (SC_list.size() <= UC_list.size() && flag==false) {
    //     while (!SC_list.empty()) {
    //         flag = false;
    //         Instruction *SC_Inst = *SC_list.begin();
    //         SC_list.erase(SC_Inst);
    //         if (UC_list.count(SC_Inst) > 0) {
    //             flag = true;
    //         }
    //         if (!flag) {
    //             break;
    //         }
    //     }
    // }
    return flag;
}

// Tries to remove a sanity check; returns true if it worked.
void DynPass::optimizeCheckAway(Instruction *Inst) {
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



void DynPass::getAnalysisUsage(AnalysisUsage& AU) const {
    AU.addRequired<SCIPass>();
    AU.setPreservesAll();
}


char DynPass::ID = 0;
static RegisterPass<DynPass> X("DynPass",
        "Finds costs of sanity checks", false, false);



