//===- HOFG.cpp - Code for generating HOFG ---------------===//
// The code flow is planned as:
// Iterate on functions : from runOnModule pass
/*
Starts with function: generateSummary(Module M)
    generates summary for each function with constructHOFGfun(Function F):
    when a call statement in a function occurs:
        applyFunctionSummary handles it:
            if the called function does not already have a summary:
                generateFunctionSummary handles it and applies the summary to call site.

*/


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
        enum vertexType {obj,ptr,snk}; //obj: new heap object, ptr: pointer, snk: free statement
        enum funcType {allocator,deallocator,allocdealloc};
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
            Value *condition;
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
            Function *funcName; //pointer to the function
            funcType functionType; //Indicate the nature of the function - allocator,deallocator,allocdealloc
            std::set<Value*> formalArgs; //List of formal arguments to the function
            std::list<funcType> argTransforms; //Transformation of arguments : on function execution, if the function allocates or deallocates any location
            Type *retType; //return type of the function
        };
        struct predBB {
            BasicBlock *bb;
            std::set<BasicBlock*> preds;
            std::set<Value*> entriConditions;
            bool operator == (const predBB &other) const {return bb == other.bb;}
            bool operator < (const predBB &other) const {return bb < other.bb;}
        };
        std::set<FuncSummary> allFuncSummaries; //set of all function summaries
        std::set<V>::iterator vit;
        std::set<predBB> allBBs; //set of all basic blocks and their predecessors
        struct E {
            std::set<F> flows;
            std::set<R> derefs;
            std::set<D> derived;
        };
	    bool runOnModule(Module &M) override {//Module pass
            errs()<<"Entered module pass";
            
            //HOFGraph P;
            //do { // loop until no change in HOFG
            //    errs()<<"\n ///////////////////////////////////////////////////////////// \n";
            //    P=HeapOFGraph;
            //    constructHOFG(M);
            //    errs()<<".........................................................";
            //    printHOFG();
            //    errs()<<".........................................................";
            //} while (! (HeapOFGraph == P));
            //P=HeapOFGraph;
            //constructHOFG(M);
            /*
            Function : generateSummary(Module &M)
            Input : Module
            Output: HOFG of the module*/
            HOFGraph P;
            do {
                P=HeapOFGraph;
                generateSummary(M);
            } while (! (HeapOFGraph == P));
             //Starting point 
            /*
            Function : printHOFG
            Output : Prints the generated HOFG : edges and vertices
            */
            printHOFG();
            //traverseCallGraph(M);
            return true;
	    };
        void printHOFG() { //To print generated HOFG
            errs()<<"\nPrinting HOFG : edges\n";
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
            errs()<<"\nPrinting HOFG: vertices\n";
            for (V e : HeapOFGraph.vertices) {
                e.name->dump();
                errs()<<"\n";
            }
        }
        void constructHOFG(Function &F) {
            //for(Module::iterator MI=M.begin();MI!=M.end();++MI) {
            //    Function &F(*MI);
                constructHOFGfun(F);
            //}
        }
        void generateSummary(Module &M) {
            for(Module::iterator MI=M.begin();MI!=M.end();++MI) {
                Function &F(*MI);
                /*
                Function : constructHOFGfun(Function &F)
                Input : function
                Output : HOFG of the function
                */
                constructHOFGfun(F);
                LLVMContext& C=F.getContext();
                MDNode* N=MDNode::get(C, MDString::get(C,"summary generated"));
                F.setMetadata("summary",N);
            }
        }
        void generateFunctionSummary(Function &F) { //generate HOFG of the function
            //constructHOFGfun(F);
            int argInx=0;
            errs()<<"\n Function with args : " << F.getName()<<"\n";
            for (auto& A : F.args()) {
                //A.dump();
                
                if(A.hasName()) {
                    Value *argValue = dyn_cast<Value>(F.getArg(argInx));
                    if(isa<PointerType>(argValue->getType())) {
                        V argNode;
                        argNode.name=argValue;
                        errs()<<"\n showing the argument : ";
                        argValue->dump();
                        //argNode.vertexTy=obj;

                        if(HeapOFGraph.vertices.find(argNode) != HeapOFGraph.vertices.end()) {
                            errs()<<"\n It in here !!!!!!!!!!!!!!!!!!!!!!!!!!!!!1";
                        }
                    }
                }
                argInx++;
            }
        }
        void constructHOFGfun(Function &F) {
            if(! F.isDeclaration()) {
                FuncSummary newFunc;
                newFunc.funcName=&F;
                newFunc.retType=F.getReturnType();
                int numargs=0;
                for (auto& A : F.args()) {
                    newFunc.formalArgs.insert(&A);
                }
                //Need to find out function type : (alloc,dealloc or allocdealloc) and argtransforms
                for(Function::iterator FI=F.begin(); FI!=F.end(); FI++) {
                    BasicBlock &B(*FI);
                    predBB newPredSet;
                    newPredSet.bb=&B;
                    auto bt=pred_begin(&B);
                    auto et=pred_end(&B);
                    //errs()<<"\npreds of BB "<<B.getName()<<" are\n";
                    for (bt = pred_begin(&B), et = pred_end(&B); bt != et; ++bt)
                    {
                        BasicBlock* predecessor = *bt;
                        Instruction* terminator = predecessor->getTerminator();
                        if(isa<BranchInst>(terminator)) {
                            BranchInst* br = dyn_cast<BranchInst>(terminator);
                            if(br->isConditional()) {
                                Value *cond= br->getCondition();
                                //cond->dump();
                                for(BasicBlock* s : br->successors()) {
                                    if(s->getName() == B.getName()) {
                                        newPredSet.entriConditions.insert(cond);
                                        //errs()<<"Condition is for "<<s->getName()<<"\n";
                                    }
                                }

                            }
                        }
                        newPredSet.preds.insert(predecessor);
                        predBB ifExistPreds;
                        ifExistPreds.bb = predecessor;
                        if(allBBs.find(ifExistPreds) != allBBs.end()) {
                            //errs()<<"Found an existing entry for bb";
                            ifExistPreds = *(allBBs.find(ifExistPreds));
                            for(BasicBlock *p : ifExistPreds.preds) {
                                newPredSet.preds.insert(p);
                            }
                            for (Value *c : ifExistPreds.entriConditions) {
                                newPredSet.entriConditions.insert(c);
                            }
                        }
                        //errs()<< "\nBBname: "<< predecessor->getName()<<"\n";
                    }
                    allBBs.insert(newPredSet);
                    /*
                    Function : idRelevantCodeSegment(BasicBlock B)
                    Input : Basic Block
                    Output : Identify the code segments in Basic Block that complies to the rules in the algorithm and invoke corresponding handlers
                    */
                    idRelevantCodeSegment(B);
                }
                errs()<<"\nPrinting predecessors of BBs";
                for (predBB b: allBBs) {
                    errs()<<"\nFor BB"<<b.bb->getName()<<" :\n";
                    for (BasicBlock* p: b.preds) {
                        errs()<<p->getName()<<"\n";
                    }
                    for (Value *c : b.entriConditions) {
                        errs()<<c->getName()<<"\n";
                    }
                }
            }
        }

        void idRelevantCodeSegment(BasicBlock &B) {//Detects the relevent code segment that needs action in the algorithm
            for(BasicBlock::iterator BI=B.begin(); BI!=B.end(); BI++) {
                Instruction &I(*BI);
                if(isMallocFunction(I)) {
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
                if(identifyFunctionCall(I)) {
                    handleRelevantCodeSegment(FUNC_CALL, B, I);
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
        bool identifyFunctionCall(Instruction &I) {
            //if(isa<BitCastInst>(I)) {
                if(isa<CallInst>(I)) {
                    CallInst *call=dyn_cast<CallInst>(&I);
                    Function *F = call->getCalledFunction();
                    if(! F->isDeclaration()) {
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
                //errs()<<"\nload..";
                //I.dump();
                if(!isa<GetElementPtrInst>(I.getOperand(0)) && isa<PointerType>(I.getType())) {
                    //errs()<<"\n Load correctly identified \n";
                    //I.dump();
                    return true;
                }
                return false;
            } else if (isa<BitCastInst>(&I)) {
                if(isa<PointerType>(I.getOperand(0)->getType())) {                    
                    //errs()<<" \n copy via bitcast : ";
                    //I.dump();
                    //return true;
                }
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
            return false;
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
        /*
        Function : handleRelevantCodeSegment (int Option, BasicBlock &B, Instruction &I)
        Input : identification of code segment, basic block and instruciton pointer
        Output : Invoke corresponding function that adds the vertices and edges to HOFG.
        */
        void handleRelevantCodeSegment(int option, BasicBlock &B, Instruction &I) { //case handler of code segments that are relevent to algorithm
            //errs()<<"\n Reached in handler : "<< B.getName();
///            errs()<<"\n function name: "<< B.getParent()->getName();
            switch (option) {
                case MEM_ALLOC: //errs()<<"\nfound malloc";
                                addMalloc(B,I); //implemented
                                break;
                case MEM_DEALLOC : //errs()<<"\nfound dealloc";
                                addDealloc(B,I); //implemented
                                break;
                case K_COPY : //errs()<<"copy into a known pointer";
                                addCopy(B,I); //implemented
                                break;
                case DEREF : //errs()<<"\n found a dereference";
                                addDereference(B,I);
                                break;
                case STORE : //errs()<<"\nstore instruction";
                                addStoreToDereference(B,I); //implemented
                                break;
                case PHI_COPY : addPhiInstruction(B,I); //implemented
                                break;
                case FUNC_CALL : applyFunctionSummary(B,I); //Ongoing
                                break;
                default : errs()<<"\ninvalid instruction"<<option;
            }
        }
        void addMalloc(BasicBlock &B, Instruction &I) {
            //errs()<<"\n Adding malloc into HOFG\n";
            V objNode,ptrNode;
            objNode.name=dyn_cast<Value>(&I);
            //objNode.name->dump();
            objNode.vertexTy=obj;
            //HeapOFGraph.vertices.insert(objNode);
            for(BasicBlock::iterator BI=B.begin(); BI!=B.end(); BI++) {
                Instruction &Ins(*BI);
                if(dyn_cast<Instruction>(Ins.getOperand(0)) == &I) {
                    if(isa<BitCastInst>(Ins)) {//for two level pointers, there can be load statement instead of bitcast befor malloc
                        ptrNode.name=dyn_cast<Value>(&Ins);
                        ptrNode.vertexTy=ptr;
                        HeapOFGraph.vertices.insert(objNode);
                        HeapOFGraph.vertices.insert(ptrNode);
                        F flowEdge;
                        flowEdge.head=ptrNode;
                        flowEdge.tail=objNode;
                        if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                        //    errs()<<"\nRepeat can be detected here";
                        } else {
                        HeapOFGraph.flows.insert(flowEdge);
                        //errs()<<"\n Adding flow edge while handling malloc : \n";
                        //I.dump();
                        //errs()<<"\n to \n";
                        //Ins.dump();
                        //errs()<<"...................";
                        }
                    } else if (isa<LoadInst>(Ins)) {
                        //To be handled for two level pointers
                    } else if (isa<StoreInst>(Ins)) {
                        errs()<<"\n detected store \n";
                        ptrNode.name=dyn_cast<Value>(Ins.getOperand(1));
                        if(HeapOFGraph.vertices.find(ptrNode) != HeapOFGraph.vertices.end()) {
                            errs()<<"\n Its already here ...";
                            ptrNode.name->dump();
                        }
                    }
                } else {
                    HeapOFGraph.vertices.insert(objNode); //malloc funciton is calle, but not used
                }
            }
        }
        void addDealloc(BasicBlock &B, Instruction &I) {
            V freeNode,ptrNode;
            freeNode.name=dyn_cast<Value>(&I);
            freeNode.vertexTy=snk;
            if (HeapOFGraph.vertices.find(freeNode) != HeapOFGraph.vertices.end()) {
                vit=HeapOFGraph.vertices.find(freeNode);
                freeNode = *vit;
                //freeNode.name->dump();
            } else {
                //if(! (HeapOFGraph.vertices.insert(freeNode).second)) {
                    //errs()<<"\nHere is the real culprit";
                //}
            }
            for(BasicBlock::iterator BI=B.begin(); BI!=B.end(); BI++) {
                Instruction &Ins(*BI);
                if(dyn_cast<Instruction>(I.getOperand(0)) == &Ins) {
                    if(isa<BitCastInst>(Ins)) {//for 2 level pointers, there can be load instead of bitcast as operand of free
                        //errs()<<"\n It reached in a bitcast detection \n";
                        ptrNode.name=dyn_cast<Value>(&Ins);
                        //ptrNode.name->dump();
                        ptrNode.vertexTy=ptr;
                        if (HeapOFGraph.vertices.find(ptrNode) != HeapOFGraph.vertices.end()) {
                            //errs()<<"It is already there in here";
                            vit=HeapOFGraph.vertices.find(ptrNode);
                            ptrNode = *vit;
                            //errs()<<"\n and it is : \n";
                            //ptrNode.name->dump();
                        } else {
                            if(! HeapOFGraph.vertices.insert(ptrNode).second) {
                                //errs()<<"\n now it is totaly wrong";
                            }
                        }
                        F flowEdge;
                        flowEdge.tail=ptrNode;
                        flowEdge.head=freeNode;
                        //if (! (HeapOFGraph.flows.insert(flowEdge).second)) { .insert.second will return if the insertion is successful
                            //errs()<<"Here it didnt work";
                        //}
                        if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                        //    errs()<<"\nRepeat can be detected here";
                        } else { 
                            HeapOFGraph.flows.insert(flowEdge);
                        }
                        //errs()<<"\n Adding flow edge while handling dealloc : \n";
                        //Ins.dump();
                        //errs()<<"\n to \n";
                        //I.dump();
                        //errs()<<"...................";
                    } else if (isa<LoadInst>(Ins)) {
                        //errs()<<"Its here : ";
                        //Ins.dump();
                        //Ins.getOperand(0)->dump();
                        //To be handled for two level pointers
                    }
                }
            }
        }
        void addCopy(BasicBlock &B, Instruction &I) {
            V srcNode, destNode;
            srcNode.name=dyn_cast<Value>(I.getOperand(0));
            srcNode.vertexTy=ptr;
            if(HeapOFGraph.vertices.find(srcNode) != HeapOFGraph.vertices.end()) {
                //errs()<<"\n Inside copy : of ";
                //I.dump();
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
                flowEdge.head=destNode;
                flowEdge.tail=srcNode;
                if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                        //    errs()<<"\nRepeat can be detected here";
                        } else {
                HeapOFGraph.flows.insert(flowEdge);
                        }
            } else {
                errs()<<"\n Found as not an exising vertex!!!";
                I.dump();
            }
        }
        void addPhiInstruction(BasicBlock &B, Instruction &I) {
            PHINode *Phi = dyn_cast<PHINode>(&I);
            //Phi->dump();
            //errs()<<"\n Processing phi instruction \n";
            //errs()<<Phi->getNumIncomingValues()<<"...\n";
            int l=Phi->getNumIncomingValues();
            V destNode;
            destNode.name=dyn_cast<Value>(&I);
            destNode.vertexTy=ptr;
            for (int i=0; i<l; i++) {
                //Phi->getIncomingValue(i)->dump();
//               errs()<<"\n ......\n";
                V srcNode;
                BasicBlock *src = Phi->getIncomingBlock(i);
                srcNode.name=dyn_cast<Value>(Phi->getIncomingValue(i));
                if(HeapOFGraph.vertices.find(srcNode) != HeapOFGraph.vertices.end()) {
                    //errs()<<"\n Found an existing node !!! \n";
                    if(HeapOFGraph.vertices.find(destNode) != HeapOFGraph.vertices.end()) {
                    //This is a copy to existing node.
                //    vit=HeapOFGraph.vertices.find(destNode);
                //    destNode = *vit;
                    } else {
                        HeapOFGraph.vertices.insert(destNode);
                    }
                    F flowEdge;
                    flowEdge.head=destNode;
                    flowEdge.tail=srcNode;
                    flowEdge.condition=src;
                    if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                        //    errs()<<"\nRepeat can be detected here";
                        } else {
                    HeapOFGraph.flows.insert(flowEdge);
                        }
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
                if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                        //    errs()<<"\nRepeat can be detected here";
                        } else {
                HeapOFGraph.flows.insert(flowEdge);
                        }
            }
        }
        void applyFunctionSummary(BasicBlock &B, Instruction &I) {
            CallInst *call=dyn_cast<CallInst>(&I);
            Function *F = call->getCalledFunction();
            if(F->hasMetadata("summary")) {
                applySummary(*F);
            } else {
                generateFunctionSummary(*F);
            }
            //applySummary(F,B,I); to be implemented
        }
        void applySummary(Function &F) {

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
