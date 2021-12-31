//===- HOFG.cpp - Code for generating HOFG ---------------===//
//
//

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Value.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Pass.h"
#include <llvm/ADT/DepthFirstIterator.h>
#include <llvm/ADT/BreadthFirstIterator.h>
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include "HOFG.def"
#include <set>
#include <cstdlib>
using namespace llvm;

#define DEBUG_TYPE "hello"
#define MALLOC "malloc"

namespace {
	//Hello3 this is for trying out various functions
	struct HOFG : public ModulePass {
        static char ID;
	    HOFG() : ModulePass(ID) {}
        enum vertexType {obj,ptr,snk,oos};
        struct V{
            Value *name;
            vertexType *type;
        };
        struct F {
            V *head;
            V *tail;
        };
        struct R {
            V *head;
            V *tail;
        };
        struct D {
            V *head;
            V *tail;
        };
        struct HOFGraph {
            std::set<V> vertices;
            std::set<F> flows;
            std::set<R> derefs;
            std::set<D> derived;
        };
        struct E {
            std::set<F> flows;
            std::set<R> derefs;
            std::set<D> derived;
        };
	    bool runOnModule(Module &M) override {
            errs()<<"Entered module pass";
            constructHOFG(M);
            traverseCallGraph(M);
            return true;
	    };
        void constructHOFG(Module &M) {
            for(Module::iterator MI=M.begin();MI!=M.end();++MI) {
                Function &F(*MI);
                constructHOFGfun(F);
            }
        }
        void constructHOFGfun(Function &F) {
            for(Function::iterator FI=F.begin(); FI!=F.end(); FI++) {
                BasicBlock &B(*FI);
                idRelevantCodeSegment(B);
            }
        }

        void idRelevantCodeSegment(BasicBlock &B) {
            for(BasicBlock::iterator BI=B.begin(); BI!=B.end(); BI++) {
                Instruction &I(*BI);
                if(isMallocFunction(I)) {
                    handleRelevantCodeSegment(MEM_ALLOC, B);                    
                }
                if(identifyCopyInstruction(I)) {
                    handleRelevantCodeSegment(K_COPY, B);
                }
                if(identifyLoadInstruction(I)) {
                    handleRelevantCodeSegment(LK_DEREF,B);
                }
                if(identifyStoreInstruction(I)) {
                    handleRelevantCodeSegment(STORE,B);
                }
                handleRelevantCodeSegment(I.getOpcode(), B);
            }
        }
        bool isMallocFunction(Instruction &I) {
            if(isa<BitCastInst>(I)) {
                if(isa<CallInst>(I.getOperand(0))) {
                    CallInst *call=dyn_cast<CallInst>(I.getOperand(0));
                    Function *F = call->getCalledFunction();
                    if(F->getName() == MALLOC) {
                        return true;
                    }
                }
            }
            return false;
        }

        void identifyCopyInstruction(Instruction &I) {
            //store preceeded by load, for pointer types
            //p=q
            if(StoreInst *storIns = dyn_cast<StoreInst>(&I)){
                if(isa<LoadInst>(storIns->getOperand(0)) && isa<PointerType>(storIns->getOperand(0)->getType())) {
                    LoadInst *old = dyn_cast<LoadInst>(storIns->getOperand(0));
                    if(isa<LoadInst>(old->getOperand(0)) || isa<LoadInst>(storIns->getOperand(1))) {
                        //Not a copy it is either a load or store constraint
                    } else {
                        return true;
                    }
                }
            }
            return false;
        }

        void identifyLoadInstruction(Instruction &I) {
            if(StoreInst *storIns = dyn_cast<StoreInst>(&I)){
                if(isa<LoadInst>(storIns->getOperand(0)) && isa<PointerType>(storIns->getOperand(0)->getType())) {
                    if(isa<LoadInst>(storIns->getOperand(1)) && isa<PointerType>(storIns->getOperand(1)->getType())) {
                        errs()<<"Load of two pointer types\n";
                        return true;
                    }
                }
            }
            return false;
        }

        void identifyStoreInstruction(Instruction &I) {
            if(StoreInst *storIns = dyn_cast<StoreInst>(&I)){
                if(isa<LoadInst>(storIns->getOperand(0)) && isa<PointerType>(storIns->getOperand(0)->getType())) {
                    Instruction* load1=dyn_cast<Instruction>(storIns->getOperand(0));
                    if(isa<LoadInst>(load1->getOperand(0)) && isa<PointerType>(load1->getOperand(0)->getType())) {
                        return true;
                    }
                }
            }
            return false;
        }

        void handleRelevantCodeSegment(int option, BasicBlock &B) {
            errs()<<"\n Reached in handler : "<< B.getName();
///            errs()<<"\n function name: "<< B.getParent()->getName();
            switch (option) {
                case MEM_ALLOC: errs()<<"\nfound malloc";
                                break;
                case MEM_DEALLOC : errs()<<"\nfound dealloc";
                                break;
                case K_COPY : errs()<<"copy into a known pointer";
                                break;
                case U_COPY : errs()<<"copy into an unknown pointer";
                                break;
                case DEREF : errs()<<"\n found a dereference";
                                break;
                case LK_DEREF : errs()<<"\nload with known dereference";
                                break;
                case LU_DEREF : errs()<<"\nload with unknown dereference";
                                break;
                case STORE : errs()<<"\nstore instruction";
                                break;
                default : errs()<<"\ninvalid instruction";
            }
        }
        void traverseCallGraph(Module &M) {
            //for (CallGraph::iterator CGI=CallGraph(M).begin(); CGI!=CallGraph(M).end(); CGI++) {
            for (auto &CGI : CallGraph(M)) {
                errs()<<"\nlooped once";
                if (const Function *F = CGI.first) {
                    errs()<<"\n Function name : "<<F->getName();
                    errs()<<"\n number of references : "<< CGI.second->getNumReferences();
                    for(auto &Vec : CGI.second->CalledFunctionsVector) {
                        errs()<<"\n are for Function " <<Vec.second->getFunction()->getName();
                    }
                } else {

                }
                errs()<<"\n.........................................\n";
            }
            errs()<<"\nDumping call graph\n";
            CallGraph(M).dump();
        }
        void getAnalysisUsage(AnalysisUsage &AU) const override {
          AU.setPreservesAll();
        }
    };
}

char HOFG::ID = 0;
static RegisterPass<HOFG> X("-analyseHOFG", "HOFG generate and analyse errors on module");
