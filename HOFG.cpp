//===- Hofg.cpp - Code for generating HOFG ---------------===//
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
	    bool runOnModule(Module &M) override {
            errs()<<"Entered module pass";
            constructHOFG(M);
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
                handleRelevantCodeSegment(I.getOpcode(), B);
            }
        }

        void handleRelevantCodeSegment(int option, BasicBlock &B) {
            errs()<<"\n Reached in handler : "<< B.getName();
            errs()<<"\n function name: "<< B.getParent()->getName();

        }
        
        void getAnalysisUsage(AnalysisUsage &AU) const override {
          AU.setPreservesAll();
        }
    };
}

char HOFG::ID = 0;
static RegisterPass<HOFG> X("-analyseHOFG", "HOFG generate and analyse errors on module");
