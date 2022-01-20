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
#include "llvm/IR/Attributes.h"
#include "llvm/Pass.h"
#include <llvm/ADT/DepthFirstIterator.h>
#include <llvm/ADT/BreadthFirstIterator.h>
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include "HOFG.def"
#include <set>
#include <cstdlib>
using namespace llvm;

namespace {
	//Hello3 this is for trying out various functions
	struct HOFG : public ModulePass {
        static char ID;
	    HOFG() : ModulePass(ID) {}
        enum vertexType {obj,ptr,snk,oos};
        enum funcType {allocator,deallocator,alldeall};
        struct V{
            Value *name;
            vertexType vertexTy;
            bool operator < (const V &other) const {return name < other.name;}
            bool operator > (const V &other) const {return name > other.name;}
            bool operator == (const V &other) const {return (name == other.name);}
        };
        struct F {
            V head;
            V tail;
            bool operator < (const F &other) const {return ((head < other.head) || (tail < other.tail));}
            bool operator > (const F &other) const {return ((head > other.head) || (tail > other.tail));}
            bool operator == (const F &other) const {return ((head == other.head) && (tail == other.tail));}
        };
        struct R {
            V head;
            V tail;
            bool operator < (const R &other) const {return ((head < other.head) || (tail < other.tail));}
            bool operator > (const R &other) const {return ((head > other.head) || (tail > other.tail));}
            bool operator == (const R &other) const {return ((head == other.head) && (tail == other.tail));}
        };
        struct D {
            V head;
            V tail;
            bool operator < (const D &other) const {return ((head < other.head) || (tail < other.tail));}
            bool operator > (const D &other) const {return ((head > other.head) || (tail > other.tail));}
            bool operator == (const D &other) const {return ((head == other.head) && (tail == other.tail));}
        };
        struct HOFGraph {
            std::set<V> vertices;
            std::set<F> flows;
            std::set<R> derefs;
            std::set<D> derived;
            bool operator == (const HOFGraph &other) const {return ((vertices == other.vertices)
            &&(flows == other.flows) && (derefs == other.derefs) && (derived == other.derived));}
        }HeapOFGraph;
        struct FuncSummary {
            Value funcName;
            std::list<funcType> args;
        };
        std::set<V>::iterator vit;
        struct E {
            std::set<F> flows;
            std::set<R> derefs;
            std::set<D> derived;
        };
	    bool runOnModule(Module &M) override {
            errs()<<"Entered module pass";
            generateSummary(M);
            HOFGraph P;
            do {
                errs()<<"\n ///////////////////////////////////////////////////////////// \n";
                P=HeapOFGraph;
                constructHOFG(M);
            //    errs()<<".........................................................";
            //    printHOFG();
            //    errs()<<".........................................................";
            } while (! (HeapOFGraph == P));
            //P=HeapOFGraph;
            //constructHOFG(M);
            printHOFG();
            
            traverseCallGraph(M);
            return true;
	    };
        void printHOFG() {
            errs()<<"\nPrinting HOFG : \n";
            for (F e : HeapOFGraph.flows) {
                e.tail.name->dump();
                errs()<<"-->";
                e.head.name->dump();
                errs()<<"\n";
            }
            for (R e : HeapOFGraph.derefs) {

            }
            for (D e : HeapOFGraph.derived) {

            }
        }
        void constructHOFG(Module &M) {
            for(Module::iterator MI=M.begin();MI!=M.end();++MI) {
                Function &F(*MI);
                constructHOFGfun(F);
            }
        }
        void generateSummary(Module &M) {
            for(Module::iterator MI=M.begin();MI!=M.end();++MI) {
                Function &F(*MI);
                generateFunctionSummary(F);
            }
        }
        void generateFunctionSummary(Function &F) {
            errs()<<"\nArguments of function : "<<F.getName()<<"\n";
            if(F.hasLazyArguments()){
                errs()<<"\n This function has lazy arguments";
            }
            int argInx=0;
            for (auto& A : F.args()) {
                A.dump();
                if(A.hasName()) {
                    Value *argValue = dyn_cast<Value>(F.getArg(argInx));
                    if(isa<PointerType>(argValue->getType())) {
                        
                    }
                }
                argInx++;
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
                    //errs()<<"\nReached here... : ";
                    //I.dump();
                    handleRelevantCodeSegment(MEM_ALLOC, B, I);                    
                }
                if(isFreeFunction(I)) {
                    handleRelevantCodeSegment(MEM_DEALLOC, B, I);
                }
                if(identifyCopyInstruction(I)) {
                    handleRelevantCodeSegment(K_COPY, B, I);
                }
                if(identifyLoadInstruction(I)) {
                    handleRelevantCodeSegment(LK_DEREF,B, I);
                }
                if(identifyStoreInstruction(I)) {
                    handleRelevantCodeSegment(STORE,B, I);
                }
                if(identifyDeallocation(I)) {
                    handleRelevantCodeSegment(DEREF, B, I);
                }
                if(isa<PHINode>(I)) {
                    handleRelevantCodeSegment(PHI_COPY, B, I);
                }
               // handleRelevantCodeSegment(I.getOpcode(), B);
            }
        }
        bool isMallocFunction(Instruction &I) {
            //if(isa<BitCastInst>(I)) {
                if(isa<CallInst>(I)) {
                    CallInst *call=dyn_cast<CallInst>(&I);
                    Function *F = call->getCalledFunction();
                    if(F->getName() == MALLOC) {
                        return true;
                    }
                }
            //}
            return false;
        }

        bool isFreeFunction(Instruction &I) {
            //if(isa<BitCastInst>(I)) {
                if(isa<CallInst>(I)) {
                    CallInst *call=dyn_cast<CallInst>(&I);
                    Function *F = call->getCalledFunction();
                    if(F->getName() == FREE) {
                        return true;
                    }
                }
            //}
            return false;
        }

        bool identifyCopyInstruction(Instruction &I) {
            //store preceeded by load, for pointer types
            //p=q
            //if(StoreInst *storIns = dyn_cast<StoreInst>(&I)){
            //    if(isa<LoadInst>(storIns->getOperand(0)) && isa<PointerType>(storIns->getOperand(0)->getType())) {
            //        LoadInst *old = dyn_cast<LoadInst>(storIns->getOperand(0));
            //        if(isa<LoadInst>(old->getOperand(0)) || isa<LoadInst>(storIns->getOperand(1))) {
                        //Not a copy it is either a load or store constraint
            //        } else {
            //            return true;
            //        }
            //    }
            //}
            //return false;
            //To do: check for load instruction.
            if(isa<LoadInst>(&I)) {
                if(!isa<GetElementPtrInst>(I.getOperand(0)) && isa<PointerType>(I.getType())) {
                    //errs()<<"\n Load correctly identified \n";
                    //I.dump();
                    return true;
                }
                return false;
            }
            return false;
        }

        bool identifyLoadInstruction(Instruction &I) {
        //    if(StoreInst *storIns = dyn_cast<StoreInst>(&I)){
        //        if(isa<LoadInst>(storIns->getOperand(0)) && isa<PointerType>(storIns->getOperand(0)->getType())) {
        //            if(isa<LoadInst>(storIns->getOperand(1)) && isa<PointerType>(storIns->getOperand(1)->getType())) {
        //                //errs()<<"Load of two pointer types\n";
        //                return true;
        //            }
        //        }
        //    }
        //    return false;
        }

        bool identifyStoreInstruction(Instruction &I) {
            if(StoreInst *storIns = dyn_cast<StoreInst>(&I)){
                if(isa<PointerType>(I.getOperand(0)->getType())) {
                    return true;
                }
            }
            return false;
        }

        bool identifyDeallocation(Instruction &I) {
            //if(isa<LoadInst>(&I)) {
            //    LoadInst *Ins = dyn_cast<LoadInst>(&I);
            //    if(isa<PointerType>(Ins->getOperand(0)->getType()) && !isa<GetElementPtrInst>(Ins->getOperand(0))) {
            //        return true;
            //    }
            //}
            return false;
        }

        void handleRelevantCodeSegment(int option, BasicBlock &B, Instruction &I) {
            //errs()<<"\n Reached in handler : "<< B.getName();
///            errs()<<"\n function name: "<< B.getParent()->getName();
            switch (option) {
                case MEM_ALLOC: //errs()<<"\nfound malloc";
                                addMalloc(B,I);
                                break;
                case MEM_DEALLOC : //errs()<<"\nfound dealloc";
                                addDealloc(B,I);
                                break;
                case K_COPY : //errs()<<"copy into a known pointer";
                                addCopy(B,I);
                                break;
                case U_COPY : //errs()<<"copy into an unknown pointer";
                                addNewCopy(B,I);
                                break;
                case DEREF : //errs()<<"\n found a dereference";
                                addDereference(B,I);
                                break;
                case LK_DEREF : //errs()<<"\nload with known dereference";
                                addLoadToKnownDereference(B,I);
                                break;
                case LU_DEREF : //errs()<<"\nload with unknown dereference";
                                addLoadToUnknownDereference(B,I);
                                break;
                case STORE : //errs()<<"\nstore instruction";
                                addStoreToDereference(B,I);
                                break;
                case PHI_COPY : addPhiInstruction(B,I);
                                break;
                default : errs()<<"\ninvalid instruction";
            }
        }
        void addMalloc(BasicBlock &B, Instruction &I) {
            //errs()<<"\n Adding malloc into HOFG\n";
            V objNode,ptrNode;
            objNode.name=dyn_cast<Value>(&I);
            objNode.vertexTy=obj;
            HeapOFGraph.vertices.insert(objNode);
            for(BasicBlock::iterator BI=B.begin(); BI!=B.end(); BI++) {
                Instruction &Ins(*BI);
                if(dyn_cast<Instruction>(Ins.getOperand(0)) == &I) {
                    if(isa<BitCastInst>(Ins)) {//for two level pointers, there can be load statement instead of bitcast befor malloc
                        ptrNode.name=dyn_cast<Value>(&Ins);
                        ptrNode.vertexTy=ptr;
                        HeapOFGraph.vertices.insert(ptrNode);
                        F flowEdge;
                        flowEdge.head=ptrNode;
                        flowEdge.tail=objNode;
                        HeapOFGraph.flows.insert(flowEdge);
                        //errs()<<"\n Adding flow edge while handling malloc : \n";
                        //I.dump();
                        //errs()<<"\n to \n";
                        //Ins.dump();
                        //errs()<<"...................";
                    }
                }
            }
        }
        void addDealloc(BasicBlock &B, Instruction &I) {
            errs()<<"\n It detected a free call\n";
            V freeNode,ptrNode;
            freeNode.name=dyn_cast<Value>(&I);
            freeNode.vertexTy=snk;
            if (HeapOFGraph.vertices.find(freeNode) != HeapOFGraph.vertices.end()) { 
                errs()<<"its also here already ... but how!!!!";
                vit=HeapOFGraph.vertices.find(freeNode);
                freeNode = *vit;
                freeNode.name->dump();
            } else {
                if(! (HeapOFGraph.vertices.insert(freeNode).second)) {
                    errs()<<"\nHere is the real culprit";
                }
            }
            for(BasicBlock::iterator BI=B.begin(); BI!=B.end(); BI++) {
                Instruction &Ins(*BI);
                if(dyn_cast<Instruction>(I.getOperand(0)) == &Ins) {
                    if(isa<BitCastInst>(Ins)) {//for 2 level pointers, there can be load instead of bitcast as operand of free
                        errs()<<"\n It reached in a bitcast detection \n";
                        ptrNode.name=dyn_cast<Value>(&Ins);
                        ptrNode.name->dump();
                        ptrNode.vertexTy=ptr;
                        if (HeapOFGraph.vertices.find(ptrNode) != HeapOFGraph.vertices.end()) {
                            errs()<<"It is already there in here";
                            vit=HeapOFGraph.vertices.find(ptrNode);
                            ptrNode = *vit;
                            errs()<<"\n and it is : \n";
                            ptrNode.name->dump();
                        } else {
                            if(! HeapOFGraph.vertices.insert(ptrNode).second) {
                                errs()<<"\n now it is totaly wrong";
                            }
                        }
                        F flowEdge;
                        flowEdge.tail=ptrNode;
                        flowEdge.head=freeNode;
                        if (! (HeapOFGraph.flows.insert(flowEdge).second)) {
                            errs()<<"Here it didnt work";
                        }
                        //errs()<<"\n Adding flow edge while handling dealloc : \n";
                        //Ins.dump();
                        //errs()<<"\n to \n";
                        //I.dump();
                        //errs()<<"...................";
                    }
                }
            }
        }
        void addCopy(BasicBlock &B, Instruction &I) {
            V srcNode, destNode;
            srcNode.name=dyn_cast<Value>(I.getOperand(0));
            srcNode.vertexTy=ptr;
            if(HeapOFGraph.vertices.find(srcNode) != HeapOFGraph.vertices.end()) {
                errs()<<"\n Found as exising vertex!!!";
                vit=HeapOFGraph.vertices.find(srcNode);
                srcNode = *vit;
                destNode.name=dyn_cast<Value>(&I);
                destNode.vertexTy=ptr;
                if(HeapOFGraph.vertices.find(destNode) != HeapOFGraph.vertices.end()) {
                    //This is a copy to existing node.
                //    vit=HeapOFGraph.vertices.find(destNode);
                //    destNode = *vit;
                } else {
                    HeapOFGraph.vertices.insert(destNode);
                }
                F flowEdge;
                flowEdge.head=srcNode;
                flowEdge.tail=destNode;
                HeapOFGraph.flows.insert(flowEdge);
            } else {

            }
        }
        void addPhiInstruction(BasicBlock &B, Instruction &I) {
            PHINode *Phi = dyn_cast<PHINode>(&I);
            //errs()<<"\n Processing phi instruction \n";
            //errs()<<Phi->getNumIncomingValues()<<"...\n";
            int l=Phi->getNumIncomingValues();
            for (int i=0; i<l; i++) {
               //Phi->getIncomingValue(i)->dump();
//               errs()<<"\n ......\n";
                V srcNode, destNode;
                srcNode.name=dyn_cast<Value>(Phi->getIncomingValue(i));
                if(HeapOFGraph.vertices.find(srcNode) != HeapOFGraph.vertices.end()) {
                //    errs()<<"\n Found an existing node !!! \n";
                }
            }
        }
        void addNewCopy(BasicBlock &B, Instruction &I) {

        }
        void addDereference(BasicBlock &B, Instruction &I) {
            //errs()<<"\n Dereference instruction handler\n";
            //I.dump();
            //errs()<<"...................\n";
            //errs()<<"\nThe instruction is: ";
            //I.dump();
            //errs()<<"\n This is a dereference of : ";
            //LoadInst *ld = dyn_cast<LoadInst>(&I);
            //ld->getOperand(0)->dump();
            //errs()<<"\n...........\n";
            //To do: If 
        }
        void addLoadToKnownDereference(BasicBlock &B, Instruction &I) {
            
        }
        void addLoadToUnknownDereference(BasicBlock &B, Instruction &I) {

        }
        void addStoreToDereference(BasicBlock &B, Instruction &I) {
            StoreInst *storIns = dyn_cast<StoreInst>(&I);
            V srcNode, destNode;
            srcNode.name=dyn_cast<Value>(storIns->getOperand(0));
            if(HeapOFGraph.vertices.find(srcNode) != HeapOFGraph.vertices.end()) {
                vit=HeapOFGraph.vertices.find(srcNode);
                srcNode = *vit;
                destNode.name=dyn_cast<Value>(storIns->getOperand(1));
                destNode.vertexTy=ptr;
                if(HeapOFGraph.vertices.find(destNode) != HeapOFGraph.vertices.end()) {
                    //This is a store to existing node.
                    vit=HeapOFGraph.vertices.find(destNode);
                    destNode = *vit;
                } else {
                    HeapOFGraph.vertices.insert(destNode);
                }
                F flowEdge;
                flowEdge.tail=srcNode;
                flowEdge.head=destNode;
                HeapOFGraph.flows.insert(flowEdge);
            }
        }
        void traverseCallGraph(Module &M) {
            //for (CallGraph::iterator CGI=CallGraph(M).begin(); CGI!=CallGraph(M).end(); CGI++) {
            //for (auto &CGI : CallGraph(M)) {
            //    errs()<<"\nlooped once";
            //    if (const Function *F = CGI.first) {
            //        errs()<<"\n Function name : "<<F->getName();
            //        errs()<<"\n number of references : "<< CGI.second->getNumReferences();
                    //for(auto &Vec : CGI.second->CalledFunctionsVector) 
                    //errs()<<"\n Called funcitions vector "<< CGI.second->CalledFunctionsVector().size();
                    //}
                    //for (CalledFunctionsVector::iterator I = CGI.second->CalledFunctions.begin(); ; ++I) {
                    //    errs()<<"\nThis works\n";
                    //}
                    //for(auto &I : (CGI.second)->CalledFunctionsVector()) {
                    //    errs()<<"\n reached here";
                    //}
            //    } else {

            //    }
            //    errs()<<"\n.........................................\n";
            //}
            //errs()<<"\nDumping call graph\n";
            //CallGraph(M).dump();
        }
        void getAnalysisUsage(AnalysisUsage &AU) const override {
          AU.setPreservesAll();
        }
    };
}

char HOFG::ID = 0;
static RegisterPass<HOFG> X("-analyseHOFG", "HOFG generate and analyse errors on module");
