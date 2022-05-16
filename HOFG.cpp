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
	struct HOFG : public ModulePass {
        static char ID;
	    HOFG() : ModulePass(ID) {}
        enum vertexType {obj,ptr,snk}; //obj: new heap object, ptr: pointer, snk: free statement
        enum funcType {allocator,deallocator,allocdealloc,noop};//Summary of a function specifies the function type
        struct V{ //Data structure to store vertices
            Value *name;
            vertexType vertexTy;
            bool operator < (const V &other) const {return name < other.name;}
            bool operator > (const V &other) const {return name > other.name;}
            bool operator == (const V &other) const {return (name == other.name);}
        };
        struct F { //Data structure to store flow edges
            V head;
            V tail;
            std::set<Value*> conditions;
            int callSite;
            //std::list<int> lineNumber;
            bool operator < (const F &other) const {return ((head < other.head) || (tail < other.tail));}
            bool operator > (const F &other) const {return ((head > other.head) || (tail > other.tail));}
            bool operator == (const F &other) const {return ((head == other.head) && (tail == other.tail) && (callSite==other.callSite));}
        };
        struct R { //Data structure to store dereference edges
            V head;
            V tail;
            bool operator < (const R &other) const {return ((head < other.head) || (tail < other.tail));}
            bool operator > (const R &other) const {return ((head > other.head) || (tail > other.tail));}
            bool operator == (const R &other) const {return ((head == other.head) && (tail == other.tail));}
        };
        struct D { //Data structure to store derived flow edges
            V head;
            V tail;
            bool operator < (const D &other) const {return ((head < other.head) || (tail < other.tail));}
            bool operator > (const D &other) const {return ((head > other.head) || (tail > other.tail));}
            bool operator == (const D &other) const {return ((head == other.head) && (tail == other.tail));}
        };
        struct HOFGraph { //The graph HOFG of the input program is stored in HeapOFGraph
            std::set<V> vertices;
            std::set<F> flows;
            std::set<R> derefs;
            std::set<D> derived;
            bool operator == (const HOFGraph &other) const {return ((vertices == other.vertices)
            &&(flows == other.flows) && (derefs == other.derefs) && (derived == other.derived));}
        }HeapOFGraph;
        struct FuncSummary { //Datastructure for storing function summary
            Function *funcName; //pointer to the function
            mutable funcType functionType; //Indicate the nature of the function - allocator,deallocator,allocdealloc
            mutable std::set<Value*> formalArgs; //List of formal arguments to the function
            mutable std::list<funcType> argTransforms; //Transformation of arguments : on function execution, if the function allocates or deallocates any location
            mutable std::set<Value*> globalAlloc;//Variables that have scope outside the function that are being allocated
            mutable std::set<Value*> globalDealloc;//Variables that have scope outside the function that are being deallocted
            Type *retType; //return type of the function
            mutable std::set<Value*> returnValues;
            bool operator < (const FuncSummary &other) const {return (funcName < other.funcName);}
        };
        struct predBB { //Storing conditins and predecessors
            BasicBlock *bb;
            std::set<BasicBlock*> preds;
            std::set<Value*> entriConditions;
            bool operator == (const predBB &other) const {return bb == other.bb;}
            bool operator < (const predBB &other) const {return bb < other.bb;}
        };
        std::set<FuncSummary> allFuncSummaries; //set of all function summaries
        std::set<FuncSummary>::iterator fsit;
        std::set<V>::iterator vit;
        std::set<predBB> allBBs; //set of all basic blocks and their predecessors
        struct E { //Set of all  edges : for the time being, not used.
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
            //HOFGraph P;
            //do {
            //    errs()<<"\n iteration of hofg";
            //    P=HeapOFGraph;
                generateSummary(M); // Call to generateSummary function, with argument module.
            //} while (! (HeapOFGraph == P));
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
                //e.tail.name->dump();
                //StringRef outfile = "out.txt";
                //std::error_code EC;
                //raw_fd_ostream out(outfile, EC);
                outs()<<*(e.tail.name);
                outs()<<"-->";
                outs()<<*(e.head.name);
                outs()<<"\n";
            }
            //for (R e : HeapOFGraph.derefs) {

            //}
            //for (D e : HeapOFGraph.derived) {

            //}
            //errs()<<"\nPrinting HOFG: vertices\n";
            //for (V e : HeapOFGraph.vertices) {
            //    e.name->dump();
            //    errs()<<"\n";
            //}
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
                generateFunctionSummary(F);
            }
        }
        void generateFunctionSummary(Function &F) { //generate HOFG of the function
                /*
                Function : constructHOFGfun(Function &F)
                Input : function
                Output : HOFG of the function
                */
                
                if(F.isDeclaration()) {

                } else {
                //errs()<<"Generating summary of : "<<F.getName()<<"\n\n";
                FuncSummary summary;
                summary.funcName = &F;
                for(Argument &A : F.args()) {
                    Value *argValue = dyn_cast<Value>(&A);
                    summary.formalArgs.insert(argValue);
                }
                summary.retType= F.getReturnType();
                allFuncSummaries.insert(summary);
                LLVMContext& C=F.getContext();
                MDNode* N=MDNode::get(C, MDString::get(C,"summary generated"));
                F.setMetadata("summary",N);
                constructHOFGfun(F);
                
                
                
                //summary.argTransforms = ; Is updated while constructHOFGfun(F) above.
                //summary.functionType = ;
                if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                    fsit=allFuncSummaries.find(summary);
//                    errs()<<fsit->argTransforms.size()<<"size after generation\n";
                    if(fsit->argTransforms.size() < 1) {
                        fsit->functionType=noop;
                    } else {
                        //if(fsit->argTransforms.contains(alloc)) {
                        //    errs()<<"\n Contains works";
                        //}
                        if((find(fsit->argTransforms.begin(), fsit->argTransforms.end(), allocator) != fsit->argTransforms.end()) && 
                        find(fsit->argTransforms.begin(), fsit->argTransforms.end(), deallocator) != fsit->argTransforms.end()) {
                            fsit->functionType=allocdealloc;
                        } else if ((find(fsit->argTransforms.begin(), fsit->argTransforms.end(), deallocator) != fsit->argTransforms.end())){
                            //errs()<<"dealloc found";
                            fsit->functionType=deallocator;
                        } else if (find(fsit->argTransforms.begin(), fsit->argTransforms.end(), allocator) != fsit->argTransforms.end()) {
                            fsit->functionType=allocator;
                        }
                    }
                }
                
                }
        }
        //FuncSummary* getFunctionSummary(Function *F) {
        //    FuncSummary summary;
        //    summary.funcName=F;
        //    if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
        //        fsit = allFuncSummaries.find(summary);
        //        return (&(*fsit));
        //    }
        //}
        void constructHOFGfun(Function &F) {
            if(! F.isDeclaration()) {
                FuncSummary newFunc;
                newFunc.funcName=&F;
                newFunc.retType=F.getReturnType();
                for (auto& A : F.args()) {
                    newFunc.formalArgs.insert(&A);
                }
                // To do : Need to find out function type : (alloc,dealloc or allocdealloc) and argtransforms
                //Following for loop is to record preds of bbs and conditions
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
                //errs()<<"\nPrinting predecessors of BBs";
                //for (predBB b: allBBs) {
                //    errs()<<"\nFor BB"<<b.bb->getName()<<" :\n";
                //    for (BasicBlock* p: b.preds) {
                //        errs()<<p->getName()<<"\n";
                //    }
                //    for (Value *c : b.entriConditions) {
                //        errs()<<c->getName()<<"\n";
                //    }
                //}
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
                if(identifyReturn(I)) {
                    handleRelevantCodeSegment(RET,B,I);
                }
                if(identifyBitCast(I)) {
                    handleRelevantCodeSegment(BIT_CAST,B,I);
                }
               // handleRelevantCodeSegment(I.getOpcode(), B);
            }
        }
        bool isMallocFunction(Instruction &I) {
            //I.dump();
            //if(isa<BitCastInst>(I)) {
                if(isa<CallInst>(I)) {
                    CallInst *call=dyn_cast<CallInst>(&I);
                    //if(isa<Function>(call->getCalledFunction())) {
                    if(call->getCalledFunction() == NULL) {
                        return false;
                    }
                    if(Function *F = dyn_cast<Function>(call->getCalledFunction())) {
                        //Function *F = call->getCalledFunction();
                        //F->dump();
                        if(F->hasName()) {
                            //errs()<<F->getName();
                            //errs()<<"\n";
                            if(F->getName() == MALLOC|| F->getName() == "u_calloc") {
                                return true;
                            } else if (F->getName() ==  "xmalloc") {
                                //F->setName("malloc");
                                //return true;
                            }
                        }  else {
                        }
                    }
                }
            //}
            return false;
        }
        bool identifyFunctionCall(Instruction &I) {
            //if(isa<BitCastInst>(I)) {
                if(isa<CallInst>(I)) {
                    CallInst *call=dyn_cast<CallInst>(&I);
                    //if(call->hasName()) {
                        if(call->getCalledFunction() == NULL) {
                           return false;
                        }
                        Function *F = call->getCalledFunction();
                        if(! F->isDeclaration()) {
                            return true;
                        }
                    //} else {
                    //}
                }
            //}
            return false;
        }

        bool isFreeFunction(Instruction &I) {
            //if(isa<BitCastInst>(I)) {
                if(isa<CallInst>(I)) {
                    CallInst *call=dyn_cast<CallInst>(&I);
                    Function *F = call->getCalledFunction();
                    //if(call->hasName()) {
                        //errs()<<F->getName();
                        if(call->getCalledFunction() == NULL) {
                           return false;
                        }
                        if(F->getName() == FREE) {
                            //errs()<<"free";
                            return true;
                        }
                    //} else {
                    //}
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
            if(dyn_cast<StoreInst>(&I)){
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
        bool identifyReturn(Instruction &I) {
            if(isa<ReturnInst>(&I)){
                if(I.getNumOperands() < 1) {
                } else {
                    return true;
                }
                return false;
            }
            return false;
        }

        bool identifyBitCast(Instruction &I) {
            if(isa<BitCastInst>(&I)) {
                return true;
            }
            return false;
        }
        /*
        Function : annotateEdge (F flowEdge)
        Input : the flow edge of the HOFG
        Output : Annotate the flow edge with the conditions to be satisfied for the program to execute the statement represented by the edge.
        */
        void annotateEdge(F flowEdge) {
            BasicBlock *tail;
            if(isa<GlobalVariable>(flowEdge.tail.name)) {
                if(isa<GlobalVariable>(flowEdge.head.name)) {
                    errs()<<"global to global";
                } else {
                    tail= dyn_cast<Instruction>(flowEdge.head.name)->getParent();
                }
            } else if(isa<GlobalVariable>(flowEdge.head.name)) {
                if(isa<Argument>(flowEdge.tail.name)){
                    tail = &(dyn_cast<Argument>(flowEdge.tail.name)->getParent()->getEntryBlock());
                } else {
                    tail = dyn_cast<Instruction>(flowEdge.tail.name)->getParent();
                }
            } else if(isa<Argument>(flowEdge.tail.name)){
                tail = &(dyn_cast<Argument>(flowEdge.tail.name)->getParent()->getEntryBlock());
            }
            predBB fromBB;
            fromBB.bb = tail;
            if(allBBs.find(fromBB) != allBBs.end()) {
                fromBB = *(allBBs.find(fromBB));
                //errs()<<"\nPrinting conditions";
                for (Value *c : fromBB.entriConditions) {
                //    errs()<<"\n ";
                //    c->dump();
                    flowEdge.conditions.insert(c);
                }
            }

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
                case FUNC_CALL :applyFunctionSummary(B,I); //Ongoing
                                break;
                case RET :      addReturn(B,I);
                                break;
                case BIT_CAST : addCopy(B,I);
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
            Type *ty = I.getFunction()->getReturnType();
            if(ty->isPointerTy()) {
                //errs()<<"\n Pointer type return for this malloc\n";
            } else {
                //errs()<<"\n did not detect void\n";
            }
            for(BasicBlock::iterator BI=B.begin(); BI!=B.end(); BI++) {
                Instruction &Ins(*BI);
                if(Ins.getNumOperands()<1) {
                    continue;
                }
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
                            //for(Argument &A : I.getFunction()->args()) {
                            //    Value* arg = dyn_cast<Value>(&A);
                                //if(arg == ptrNode.name) {
                                    if(isa<Argument>(ptrNode.name)) {
                                    //errs()<<"\nhead is an arg in malloc\n";
                                    FuncSummary summary;
                                    summary.funcName = I.getFunction();
                                    if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                        fsit = allFuncSummaries.find(summary);
                                        fsit->argTransforms.push_back(allocator);
                                        //fsit->functionType=allocator;
                                    }
                                    }
                                //}
                            //}
                         annotateEdge(flowEdge);
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
                        //errs()<<"\n detected store \n";
                        ptrNode.name=dyn_cast<Value>(Ins.getOperand(1));
                        if(HeapOFGraph.vertices.find(ptrNode) != HeapOFGraph.vertices.end()) {
                            //errs()<<"\n Its already here ...";
                            //ptrNode.name->dump();
                        }
                    } else if(isa<ReturnInst>(Ins)) {
                        //To do: add appropriate vetices and edges
                    }
                } else {
                    HeapOFGraph.vertices.insert(objNode); //malloc funciton is called, but not used
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
                            //for(Argument &A : I.getFunction()->args()) {
                            //    Value* arg = dyn_cast<Value>(&A);
                                //arg->dump();
                                //ptrNode.name->dump();
                                if(isa<Argument>(ptrNode.name) || isa<Argument>(dyn_cast<Instruction>(ptrNode.name)->getOperand(0))) {
                                    //errs()<<"\ntail is an arg\n";
                                    FuncSummary summary;
                                    summary.funcName = I.getFunction();
                                    if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                        fsit = allFuncSummaries.find(summary);
                                        fsit->argTransforms.push_back(deallocator);
                                        //fsit->functionType=allocator;
                                    }
                                } else if(isa<GlobalVariable>(ptrNode.name)) {
                                    //This is a deallocation of a global variable
                                    FuncSummary summary;
                                    summary.funcName = I.getFunction();
                                    if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                        fsit = allFuncSummaries.find(summary);
                                        fsit->globalDealloc.insert(freeNode.name);
                                        //errs()<<"Global value deallocated";
                                    }
                                } else if(isa<GlobalVariable>(dyn_cast<Instruction>(ptrNode.name)->getOperand(0))) {
                                    FuncSummary summary;
                                    summary.funcName = I.getFunction();
                                    if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                        fsit = allFuncSummaries.find(summary);
                                        Value *v=dyn_cast<Value>(dyn_cast<Instruction>(freeNode.name)->getOperand(0));
                                        fsit->globalDealloc.insert(v);
                                        //errs()<<"Global value deallocated";
                                    }
                                }
                            //}
                            HeapOFGraph.vertices.insert(freeNode);
                            annotateEdge(flowEdge); 
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
                    } else {
                        ptrNode.name=dyn_cast<Value>(&Ins);
                        if (HeapOFGraph.vertices.find(ptrNode) != HeapOFGraph.vertices.end()) {
                            ptrNode=*(HeapOFGraph.vertices.find(ptrNode));
                            F flowEdge;
                            flowEdge.tail=ptrNode;
                            flowEdge.head=freeNode;
                            HeapOFGraph.vertices.insert(freeNode);
                            annotateEdge(flowEdge); 
                            HeapOFGraph.flows.insert(flowEdge);
                        }
                    }
                }
            }
        }
        void addCopy(BasicBlock &B, Instruction &I) {
            V srcNode, destNode;
            srcNode.name=dyn_cast<Value>(I.getOperand(0));
            //I.getOperand(0)->dump();
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
                            //for(Argument &A : I.getFunction()->args()) {
                            //    Value* arg = dyn_cast<Value>(&A);
                                if(isa<Argument>(destNode.name)) {
                                    //errs()<<"\nhead is an arg in copy\n";
                                    FuncSummary summary;
                                    summary.funcName = I.getFunction();
                                    if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                        fsit = allFuncSummaries.find(summary);
                                        fsit->argTransforms.push_back(allocator);
                                        //fsit->functionType=allocator;
                                    }
                                }
                            //}
                            if(isa<GlobalVariable>(flowEdge.head.name) && isa<GlobalVariable>(flowEdge.tail.name)) {
                                predBB fromBB;
                                fromBB.bb =&B;
                                if(allBBs.find(fromBB) != allBBs.end()) {
                                    fromBB = *(allBBs.find(fromBB));
                                    for (Value *c : fromBB.entriConditions) {
                                        flowEdge.conditions.insert(c);
                                    }
                                }
                            } else {
                                annotateEdge(flowEdge);
                            }
                            HeapOFGraph.flows.insert(flowEdge);
                        }
            } else {
                //errs()<<"\n Found as not an exising vertex!!!";
                //I.dump();
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
                //errs()<<"\n ......\n";
                V srcNode;
                //BasicBlock *src = Phi->getIncomingBlock(i);
                srcNode.name=dyn_cast<Value>(Phi->getIncomingValue(i));
                if(isa<Argument>(srcNode.name)) {
                    errs()<<"\n phi src detected but not catched";
                }
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
                    //flowEdge.condition=src;
                    if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                        //    errs()<<"\nRepeat can be detected here";
                        } else {
                            //for(Argument &A : I.getFunction()->args()) {
                            //    Value* arg = dyn_cast<Value>(&A);
                                if(isa<Argument>(destNode.name)) {
                                    //errs()<<"\nhead is an arg in phi\n";
                                    FuncSummary summary;
                                    summary.funcName = I.getFunction();
                                    if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                        fsit = allFuncSummaries.find(summary);
                                        fsit->argTransforms.push_back(allocator);
                                        //fsit->functionType=allocator;
                                    }
                                }
                                if(isa<Argument>(srcNode.name)) {
                                    errs()<<"\nSource of phi instruction is an argument";
                                }
                            //}
                            annotateEdge(flowEdge);
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
                if(dyn_cast<Argument>(storIns->getOperand(1))) {
                //    errs()<<"\nIts global";
                } else if(dyn_cast<Instruction>(storIns->getOperand(1))){
                //    errs()<<"\nIts an instruction";
                } else {
                //    errs()<<"\nNot casted";
                }
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
                    FuncSummary summary;
                    //for(Argument &A : I.getFunction()->args()) {
                    //    Value* arg = dyn_cast<Value>(&A);
                    //    if(arg == destNode.name) {
                    if(isa<Argument>(destNode.name)) {
                       // errs()<<"\nhead is an arg in store\n";
                        summary.funcName = I.getFunction();
                        if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                            fsit = allFuncSummaries.find(summary);
                            fsit->argTransforms.push_back(allocator);
                        //    errs()<<fsit->argTransforms.size()<<"size\n";
                        }
                    }
                    if(isa<GlobalVariable>(destNode.name)) {
                        summary.funcName = I.getFunction();
                        if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                            fsit = allFuncSummaries.find(summary);
                            //Value *v = dyn_cast<Value>(storIns->getOperand(1));
                            fsit->globalAlloc.insert(dyn_cast<Value>(storIns));
                            //errs()<<"\nglobal value allocated for function : "<<I.getFunction()->getName();
                        }
                    }
                    if(isa<Argument>(srcNode.name)) {
                        errs()<<"\n source node of store is argument";
                    }
                    //    }
                    //}
                    //errs()<<fsit->argTransforms.size()<<"size\n";
                    annotateEdge(flowEdge);
                    HeapOFGraph.flows.insert(flowEdge);
                }
            }
        }
        void addReturn(BasicBlock &B, Instruction &I) {
            Function *F=I.getFunction();
            if(F->hasMetadata("summary")) {
                FuncSummary summary;
                summary.funcName=F;
                if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                    fsit = allFuncSummaries.find(summary);
                    fsit->returnValues.insert(dyn_cast<Value>(I.getOperand(0)));
                }
            }

        }
        void applyFunctionSummary(BasicBlock &B, Instruction &I) {
            CallInst *call=dyn_cast<CallInst>(&I);
            Function *Fun = call->getCalledFunction();
            Function *caller = I.getFunction();
            if(caller == Fun) {
                //errs()<<"Recursive";
            } else {
                if(!call->args().empty()) {
                    int i,iterator=0;
                    V actualArgNode,formalArgNode;
                    for(Value *A : call->args()) {
                        i=iterator; 
                        for(Argument &B : Fun->args()) {
                            if(i==0) {
                                formalArgNode.name=dyn_cast<Value>(&B);
                            } else {
                                i--;
                                continue;
                            }
                        }
                        actualArgNode.name=A;
                        if(HeapOFGraph.vertices.find(actualArgNode) != HeapOFGraph.vertices.end()) {
                            if(HeapOFGraph.vertices.find(formalArgNode) != HeapOFGraph.vertices.end()) {
                                formalArgNode=*(HeapOFGraph.vertices.find(formalArgNode));
                            } else {
                                formalArgNode.vertexTy=ptr;
                                HeapOFGraph.vertices.insert(formalArgNode);
                            }
                            F flowEdge;
                            flowEdge.tail=actualArgNode;
                            flowEdge.head=formalArgNode;
                            HeapOFGraph.flows.insert(flowEdge);
                        }
                        iterator++;
                    }
                }
                if(Fun->hasMetadata("summary")) {
                    //errs()<<"From a call instruction, the function has summary already: "<<F->getName()<<"\n";
                    applySummary(*Fun,*call);
                } else {
                    //errs()<<"From a function call, the function does not already have a summary. So generating summary of:"<<F->getName()<<"\n";
                    generateFunctionSummary(*Fun);
                    applySummary(*Fun,*call);
                }
            }
            //applySummary(F,B,I); to be implemented
        }
        void applySummary(Function &F, CallInst &I) {
            //int argInx=0;
            //errs()<<"In apply summary of the function: "<<F.getName()<<"\n";
            //To do: Check the function summary.
            //1. summary.functionType : allocator,deallocator
            //2. summary.returnType : return value may be pointer to a newly allocated heap object.
            //3. summary.argTransforms : whether any arguments are being allocated or deallocated.
            //4. summary.returnValues : if a function returns pointer(s)
            //According to allocator or deallocator, for each function call, we need to create new nodes, using the function summary.
            FuncSummary summary;
            summary.funcName=&F;
            if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                fsit = allFuncSummaries.find(summary);
                summary=*fsit;
            }
            if(isa<PointerType>(*(summary.retType))) {
            //    errs()<<"\nPtr type return value\n";
                if(summary.functionType == allocator) {
                    //errs()<<"\nThis function allocates through return value";
                }
            } else if(summary.functionType == allocator) {
                //if(summary.argTransforms.size() > 0) {
            //    errs()<<"\nArg transforms detected\n";
                    for(funcType t: summary.argTransforms) {
                        if(t==allocator) {
                            errs()<<"\n Allocator detected";
                            //To do: add edge from formal arg to actual arg
                        } else if (t==deallocator) {
                            errs()<<"\nDeallocator detected";
                        } else if (t==noop) {
                            errs()<<"\nnoop detected";
                        }
                    }
                //}
            }
            if(summary.argTransforms.size() > 0) {
            //    errs()<<"\nArg transforms detected\n";
                for(funcType t: summary.argTransforms) {
                    if (t==deallocator) {
                        errs()<<"\nDeallocator detected";
                    }
                }
            }
            if(summary.globalAlloc.size() > 0) {
                addGlobalAlloc(summary.globalAlloc);
            //    errs()<<"\nglobal value is allocated";
            }
            if(summary.globalDealloc.size() > 0) {
                addGlobalDealloc(summary.globalDealloc);
            //    errs()<<"\nglobal value is deallocated";
            }
            if(summary.returnValues.size() > 0) {
                addReturnToCallSite(I,fsit);
            //    errs()<<"\nPointer type return values detected";
            }
        }
        void addReturnToCallSite(CallInst &I,std::set<FuncSummary>::iterator fsit ) {
            FuncSummary summary;
            summary=*fsit;
            V retNode, receiverNode;
            receiverNode.name=dyn_cast<Value>(&I);
            if(HeapOFGraph.vertices.find(receiverNode) != HeapOFGraph.vertices.end()) {
                receiverNode=*(HeapOFGraph.vertices.find(receiverNode));
            } else {
                receiverNode.vertexTy=ptr;
                HeapOFGraph.vertices.insert(receiverNode);
            }
            for(Value *ret : summary.returnValues) {
                retNode.name=ret;
                if(HeapOFGraph.vertices.find(retNode) != HeapOFGraph.vertices.end()) {
                    retNode=*(HeapOFGraph.vertices.find(retNode));
                }
            }
            F flowEdge;
            flowEdge.head=receiverNode;
            flowEdge.tail=retNode;
            annotateEdge(flowEdge);
            HeapOFGraph.flows.insert(flowEdge);
        }
        void addGlobalDealloc(std::set<Value*> deallocSet) {
            //errs()<<"Global dealloc detected: ";
            //Value *dealloc=*deallocSet.begin();
            //dealloc->dump();
            for(Value *deallocIns : deallocSet) {
                V freeNode,globalNode;
                freeNode.name=deallocIns;
                if(HeapOFGraph.vertices.find(freeNode) != HeapOFGraph.vertices.end()) {
                    freeNode=*(HeapOFGraph.vertices.find(freeNode));
                }
                Value *v=dyn_cast<Value>(dyn_cast<Instruction>(freeNode.name)->getOperand(0));
                globalNode.name=v;//dyn_cast<Value>(dyn_cast<Instruction>(deallocIns->getOperand(0)));
                if(HeapOFGraph.vertices.find(globalNode) != HeapOFGraph.vertices.end()) {
                    globalNode=*(HeapOFGraph.vertices.find(globalNode));
                }
                F flowEdge;
                flowEdge.head=freeNode;
                flowEdge.tail=globalNode;
                annotateEdge(flowEdge);
                HeapOFGraph.flows.insert(flowEdge);
            }
        }
        void addGlobalAlloc(std::set<Value*> allocSet) {
            //errs()<<"Global alloc detected: ";
            //Value *alloc=*allocSet.begin();
            //alloc->dump();
            for(Value *allocIns : allocSet) {
                V globalNode,ptrNode,objNode;
                F flowEdge1,flowEdge2;
                Value *v=dyn_cast<Value>(dyn_cast<Instruction>(allocIns)->getOperand(1));
                globalNode.name=v;//dyn_cast<Value>(dyn_cast<Instruction>(deallocIns->getOperand(0)));
                if(HeapOFGraph.vertices.find(globalNode) != HeapOFGraph.vertices.end()) {
                    globalNode=*(HeapOFGraph.vertices.find(globalNode));
                }
                if(BitCastInst *bcI = dyn_cast<BitCastInst>((dyn_cast<Instruction>(allocIns))->getOperand(0))) {
                    if(CallInst *call = dyn_cast<CallInst>(bcI->getOperand(0))) {
                        objNode.name=dyn_cast<Value>(call);
                        if(HeapOFGraph.vertices.find(objNode) != HeapOFGraph.vertices.end()) {
                            objNode=*(HeapOFGraph.vertices.find(objNode));
                            
                        }
                    }
                    ptrNode.name=dyn_cast<Value>(bcI);
                    if(HeapOFGraph.vertices.find(ptrNode) != HeapOFGraph.vertices.end()) {
                        ptrNode=*(HeapOFGraph.vertices.find(ptrNode));
                        
                    }
                    flowEdge1.tail=objNode;
                            flowEdge1.head=ptrNode;
                            annotateEdge(flowEdge1);
                            HeapOFGraph.flows.insert(flowEdge1);
                            flowEdge2.tail=ptrNode;
                        flowEdge2.head=globalNode;
                        annotateEdge(flowEdge2);
                        HeapOFGraph.flows.insert(flowEdge2);
                }
                
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
