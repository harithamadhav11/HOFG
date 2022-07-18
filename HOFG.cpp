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
#include "llvm/IR/DebugInfoMetadata.h"
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
            mutable std::set<Value*> conditions;
            DebugLoc location;
            bool operator < (const F &other) const {return ((head < other.head) || (tail < other.tail));}
            //bool operator > (const F &other) const {return ((head > other.head) || (tail > other.tail));}
            bool operator == (const F &other) const {return ((head == other.head) && (tail == other.tail) && (conditions==other.conditions));}
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
            bool operator == (const HOFGraph &other) const {return ((vertices.size() == other.vertices.size())
            &&(flows.size() == other.flows.size()));}
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
        struct HOFGpath {
            V start;
            V end;
            mutable std::set<F>pathEdge;
            bool operator == (const HOFGpath &other) const {return ((start == other.start) && (pathEdge == other.pathEdge));}
            bool operator < (const HOFGpath &other) const {return ((start < other.start) || (pathEdge != other.pathEdge));}
        };
        mutable std::set<HOFGpath> pathSet;
        std::set<HOFGpath>::iterator psit;
        std::set<FuncSummary> allFuncSummaries; //set of all function summaries
        std::set<FuncSummary>::iterator fsit;
        std::set<V>::iterator vit;
        std::list<funcType>::iterator argTransformIt;
        std::set<predBB> allBBs; //set of all basic blocks and their predecessors
        struct E { //Set of all  edges : for the time being, not used.
            std::set<F> flows;
            std::set<R> derefs;
            std::set<D> derived;
        };
	    bool runOnModule(Module &M) override {//Module pass
            errs()<<"Entered module pass";
            
            HOFGraph P;
            do { // loop until no change in HOFG
                errs()<<"\n ///////////////////////////////////////////////////////////// \n";
                P=HeapOFGraph;
                generateSummary(M);
            } while (! (HeapOFGraph == P));
            //P=HeapOFGraph;
            //constructHOFG(M);
            
            /*
            Function : printHOFG
            Output : Prints the generated HOFG : edges and vertices
            */
            printHOFG();
            generatePathsFromHOFG();
            printPaths();
            pruneLeakLessPaths();
            detectEndsOFPath();
            getMayLeakPaths();
            return true;
	    };
        void printHOFG() { //To print generated HOFG
            
            errs()<<"\nNumber of veritces : "<<HeapOFGraph.vertices.size()<<" \n";
            int allocationSites = 0;
            for (V vertex : HeapOFGraph.vertices) {
                if(vertex.vertexTy == obj) {
                    allocationSites++;
                }
            }
            //errs()<<"\nNumber of allocation sites : "<<allocationSites<<"\n";
            //for(F e : HeapOFGraph.flows) {
            //    int count =0 ;
            //    std::set<F>::iterator f=HeapOFGraph.flows.begin();
            //    for(F c : HeapOFGraph.flows) {
            //        if(e.head == c.head && e.tail == c.tail && e.conditions == c.conditions && e.location == c.location) {
            //            count++;
            //            if(count > 1) {
            //                f=HeapOFGraph.flows.find(c);
            //                HeapOFGraph.flows.erase(f);
            //            }
            //        }
            //    }
            //}
            std::set<F>::iterator f=HeapOFGraph.flows.begin();
            //std::set<F>::iterator c=HeapOFGraph.flows.begin();
            int e = HeapOFGraph.flows.size();
            int ce = e;
            while(e>1) {
                int count = 0;
                ce=HeapOFGraph.flows.size();
                std::set<F>::iterator c=f;
                while(ce>2) {
                    if((*f)==(*c)) {
                        count++;
                        if(count > 1) {
        //                    errs()<<"\nErased 1";
                            HeapOFGraph.flows.erase(c);
                            ce--;
                            e--;
                            break;
                        }
                    }
                    c++;
                    ce--;
                }
                f++;
                e--;
            }

            std::set<F>::iterator fitr=HeapOFGraph.flows.begin();
            int edgesize = HeapOFGraph.flows.size();
            int cesize = edgesize;
            while(edgesize>1) {
                int count = 0;
                cesize=HeapOFGraph.flows.size();
                std::set<F>::iterator citr=fitr;
                while(cesize>2) {
                    if(((*fitr).head==(*citr).tail) && ((*fitr).tail==(*citr).head)) {
                        count++;
                        if(count > 0) {
                            //(*citr).tail.name->dump();
                            //(*citr).head.name->dump();
                            //(*fitr).tail.name->dump();
                            //(*fitr).head.name->dump();
                            //errs()<<"\nErased 2";
                            HeapOFGraph.flows.erase(citr);
                            cesize--;
                            edgesize--;
                            break;
                        }
                    }
                    citr++;
                    cesize--;
                }
                fitr++;
                edgesize--;
            }
            std::set<F>::iterator A=HeapOFGraph.flows.begin();
            int C = HeapOFGraph.flows.size();
            int D = C;
            while(C>0) {
                int count = 0;
                D=HeapOFGraph.flows.size();
                std::set<F>::iterator B=HeapOFGraph.flows.begin();
                while(D>0) {
                    if((*A).tail==(*B).head) {
                        count++;
                    }
                    B++;
                    D--;
                }
                if(count == 0 && (*A).tail.vertexTy != obj) {
                    //errs()<<"\n reaches here for: ";
                    //(*A).tail.name->dump();
                    std::set<F>::iterator eraseEdge = A;
                    A++;
                    //errs()<<HeapOFGraph.flows.size()<<"\n";
        //            errs()<<"\nErased 4";
                    HeapOFGraph.flows.erase(eraseEdge);
                    //errs()<<HeapOFGraph.flows.size()<<"\n";
                    C--;
                } else {
                    A++;
                }
                C--;
            }
            std::set<F>::iterator sl=HeapOFGraph.flows.begin();
            std::set<F>::iterator nsl;
            int sll = HeapOFGraph.flows.size();
            while(sll > 0) {
                //errs()<<"\n checking....";
                if((*sl).head.name == (*sl).tail.name) {
                //  errs()<<"\n deleting dummy edge from head to head";
                    nsl=sl;
                    sl++;
        //            errs()<<"\nErased 5";
                    HeapOFGraph.flows.erase(nsl);
                    sll --;
                }
                sll--;
            }
            errs()<<"\nPrinting HOFG : "<<HeapOFGraph.flows.size()<< " edges\n";
            for (F e : HeapOFGraph.flows) {
                //e.tail.name->dump();
                //StringRef outfile = "out.txt";
                //std::error_code EC;
                //raw_fd_ostream out(outfile, EC);
                outs()<<*(e.tail.name);
                outs()<<"-->";
                outs()<<*(e.head.name);
                //outs()<<"\n debug location:"<<e.location.getLine()<<"\n";
                //outs()<<"\nWith condition : ";
                //for(auto v : e.conditions) {
                //    outs()<<*(v);
                //}
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
        /*
        Function : print the paths in the HOFG
        Input : The pathSet structure instance in the program
        Output : List of paths generated from the graph is printed
       */
        void printPaths() {
            errs()<<"\nNumber of paths:"<<pathList.size()<<"\n";
        }
        void printPathsList() {
            int psize = pathList.size();
            std::list<HOFGpath>::iterator p=pathList.begin();
            //for(HOFGpath p : pathSet) {
            while(psize>0){
                outs()<<"\n Starting from : ";
                //errs()<<*((*p).start.name);

                outs()<<*((*p).start.name);
                //outs()<<"\nPath edge size: "<<(*p).pathEdge.size()<<"\n";
                for (F flowEdge : (*p).pathEdge) {
                    outs()<<"-->";
                    outs()<<*(flowEdge.head.name);
                    outs()<<"\n";
                }
                outs()<<"\nEnd of path";
                psize--;
                p++;
            }
        }
        void printPathsSet() {
            errs()<<"\nNumber of paths:"<<pathSet.size()<<"\n";
            int psize = pathSet.size();
            std::set<HOFGpath>::iterator p=pathSet.begin();
            //for(HOFGpath p : pathSet) {
            while(psize>0){
                outs()<<"\n Starting from : ";
                //errs()<<*((*p).start.name);

                outs()<<*((*p).start.name);
                outs()<<"\nPath edge size: "<<(*p).pathEdge.size()<<"\n";
                for (F flowEdge : (*p).pathEdge) {
                    outs()<<"-->";
                    outs()<<*(flowEdge.head.name);
                    outs()<<"\n";
                }
                outs()<<"\nEnd of path";
                psize--;
                p++;
            }
        }
        void detectEndsOFPath() {
            std::set<V> endVertex;
            std::set<F> endEdges;
            for(HOFGpath path : pathList) {
                for(F flowEdgeInPath : path.pathEdge) {
                    bool foundLink = false;
                    for(F f : path.pathEdge) {
                        if(flowEdgeInPath.head == f.tail) {
                            foundLink = true;
                        }
                    }
                    if(!foundLink && flowEdgeInPath.head.vertexTy != snk) {
                        endVertex.insert(flowEdgeInPath.head);
                        endEdges.insert(flowEdgeInPath);
                    }
                }
            }
            errs()<<"\nEnd points : "<<endEdges.size()<<"\n";
            for(F endedge : endEdges) {
                endedge.head.name->dump();
                errs()<<"\nIn line : "<<endedge.location.getLine()<< "\n";
                auto *Scope = cast<DIScope>(endedge.location->getScope());
                std::string fileName = Scope->getFilename().str();
                errs()<<"in file : "<<fileName<<"\n";
            }
            errs()<<"\n";
        }
        void detectEndsOFPathFromHOFG() {
            std::set<V> endVertex;
            std::set<F> endEdges;
            bool endMark = false;
            int count = 0;
            for(F edgeInGraph : HeapOFGraph.flows) {
                endMark = false;
                //errs()<<"\nSearching for : ";
                //edgeInGraph.head.name->dump();
                for(F otherEdge : HeapOFGraph.flows) {
                    if(edgeInGraph.head == otherEdge.tail) {
                        //errs()<<"\nCaught";
                        endMark = true;
                    }
                }
                if(!endMark) {
                    if(edgeInGraph.head.vertexTy == snk) {

                    } else {
                        count++;
                        //errs()<<"\n End point : ";
                        //edgeInGraph.head.name->dump();
                        endVertex.insert(edgeInGraph.head);
                        endEdges.insert(edgeInGraph);
                    }
                }
            }
            errs()<<"\n "<<count<<" end edges\n";
            errs()<<"\n "<<endVertex.size()<<" end points\n";
            for(V ends : endVertex) {
                ends.name->dump();
            }
            for(F endedge : endEdges) {
                //endedge.tail.name->dump();
                //errs()<<"\nIn line : "<<endedge.location.getLine()<< "\n";
                //auto *Scope = cast<DIScope>(endedge.location->getScope());
                //std::string fileName = Scope->getFilename().str();
                //errs()<<"in file : "<<fileName<<"\n";
            }
        }
        /*
        Function : prune off paths from obj to free nodes in the HOFG
        Input : The pathSet sturct instance in the program
        Output : List of paths from the graph that can tentatively contain leak.
        A path : a sequence of pointers to the edges in the HeapOFGraph
        */
        void pruneLeakLessPaths() {
            std::list<HOFGpath>::iterator p=pathList.begin();
            std::list<HOFGpath>::iterator pnext=pathList.begin();
            int n=pathList.size();
            while(n>1) {
                //errs()<<"\n"<<n<<"\n";
                bool status = false;
                for(F edge : (*p).pathEdge) {
                    if(edge.head.vertexTy == snk && edge.conditions.size()==0) {
                        status=true;
                        break;
                    }
                }
                if(status) {
                    //errs()<<"\nDeleting\n";
                    pnext=p++;
                    pathList.erase(p);
                    n--;
                    p=pnext;
                    //errs()<<"\n size : "<<pathSet.size()<<"\n";
                } else {
                    p++;
                }
                
                n--;
            }   
        }
        void getMayLeakPaths() {
            std::list<HOFGpath> pathListCopy = pathList;
            std::list<HOFGpath>::iterator p=pathListCopy.begin();
            std::list<HOFGpath>::iterator pnext=pathListCopy.begin();
            int n=pathListCopy.size();
            while(n>1) {
                //errs()<<"\n"<<n<<"\n";
                bool status = false;
                for(F edge : (*p).pathEdge) {
                    if(edge.head.vertexTy == snk) {
                        status=true;
                        break;
                    }
                }
                if(status) {
                    pnext=p++;
                    pathListCopy.erase(p);
                    n--;
                    p=pnext;
                    //errs()<<"\n size : "<<pathSet.size()<<"\n";
                } else {
                    p++;
                }
                
                n--;
            }
            errs()<<"\nNumber of may leak paths : "<<pathListCopy.size();
        }

        void pruneLeakLessPathsSet() {
            std::set<HOFGpath>::iterator p=pathSet.begin();
            int n=pathSet.size();
            while(n>1) {
                //errs()<<"\n"<<n<<"\n";
                bool status = false;
                for(F edge : (*p).pathEdge) {
                    if(edge.head.vertexTy == snk && edge.conditions.size()==0) {
                        status=true;
                        break;
                    }
                }
                if(status) {
                    //errs()<<"\nDeleting\n";
                    pathSet.erase(p);
                    n--;
                    //errs()<<"\n size : "<<pathSet.size()<<"\n";
                }
                p++;
                n--;
            }
        }
        mutable std::list<HOFGpath> pathList;
        void generatePathsFromHOFG() {
            generateStartOfPaths();
            errs()<<"\nThe path list initially have :"<<pathList.size()<<" number of elements";
            for(HOFGpath path : pathList) {
                int outEdgeCount=0;
                HOFGpath newPath=path;
                if(path.pathEdge.size() ==0) {
                for(F edgeInGraph : HeapOFGraph.flows) {
                    if(path.start == edgeInGraph.tail) {
                        if(outEdgeCount == 0) {
                            std::list<HOFGpath>::iterator plit;
                            newPath=path;
                            plit=find(pathList.begin(),pathList.end(),path);
                            //errs()<<"\nCalled from here 1";
                            addEdgeToList(edgeInGraph,plit);
                        } else {
                            std::list<HOFGpath>::iterator plit;
                            pathList.push_back(newPath);
                            plit=find(pathList.begin(),pathList.end(),newPath);
                            //errs()<<"\nCalled from here 2";
                            addEdgeToList(edgeInGraph,plit);
                        }
                        outEdgeCount++;
                    }
                }
                }
            }
        }
        void addEdgeToList(F edgeToBeAdded, std::list<HOFGpath>::iterator plit) {
            //HOFGpath newPath = (*plit);
            bool circPath = false;
            for(F presentEdge : (*plit).pathEdge) {
                if((edgeToBeAdded.head == presentEdge.tail) || (edgeToBeAdded.head == presentEdge.head)) {
                //    errs()<<"\n Circular path edge caughr here !!!!!!!!!!!!!!!!!!!!!!!!!!!!!11!";
                    circPath = true;
                }
            }
            if(!circPath) {
                (*plit).pathEdge.insert(edgeToBeAdded);
                //errs()<<"\n added edge :";
                //edgeToBeAdded.tail.name->dump();
                //errs()<<"-->";
                //edgeToBeAdded.head.name->dump();
                //errs()<<"\nTo start: ";
                //(*plit).start.name->dump();
                //errs()<<"\n...............................................";
                int count = 0;
                HOFGpath newPath = (*plit);
                for(F edgeInGraph : HeapOFGraph.flows) {
                    if(edgeToBeAdded.head == edgeInGraph.tail) {
                        if(count == 0) {
                            //errs()<<"\nCalled from here 3";
                            addEdgeToList(edgeInGraph,plit);
                        } else {
                            std::list<HOFGpath>::iterator npit;
                            HOFGpath nextPath = newPath;
                            //errs()<<"\n Path list size : "<<pathList.size()<<"\n";
                            pathList.push_back(newPath);
                    //        errs()<<"\nPath list size after : "<<pathList.size()<<"\n";
                            npit = pathList.end();
                            npit--;
                            if(newPath == (*npit)) {
                                //errs()<<"\nCalled from here 4";
                                addEdgeToList(edgeInGraph,npit);
                            }
                        }
                        count++;
                    }
                }
            }
        }   
        void generateStartOfPaths() {
            for(V vert : HeapOFGraph.vertices) {
                if(vert.vertexTy == obj) {
                    HOFGpath newPath;
                    newPath.start = vert;
                    if(find(pathList.begin(),pathList.end(),newPath) != pathList.end()) {
                        
                    } else {
                        //vert.name->dump();
                        pathList.push_back(newPath);
                    }
                }
            }
        }
        /*
        Function : generate paths from obj to free nodes in the HOFG
        Input : The HeapOFGraph sturct instance in the program
        Output : List of paths generated from the graph.
        A path : a sequence of pointers to the edges in the HeapOFGraph
        */
        void generatePaths() {
            generatePathHeads();
            errs()<<"\nPathheads generated. \n";
            int count=0;
            std::set<HOFGpath>::iterator psit;
            outs()<<"\nInitially path heads count:"<<pathSet.size()<<"\n";
            errs()<<"\nInitially path heads count:"<<pathSet.size()<<"\n";
            for(HOFGpath p : pathSet) {
                HOFGpath newPath=p;
                errs()<<"\npathSet count becomes :"<<pathSet.size()<<"\n";
                if(pathSet.size()>1000) {
                    break;
                }
                
                count=0;
                
                if(p.pathEdge.size() == 0) {
                    for(F flowEdge : HeapOFGraph.flows) {
                        if(flowEdge.tail == p.start) {
                            psit=pathSet.find(p);
                            if(count == 0) {
                                newPath = p;
                                addToPath(flowEdge, psit);
                            } else if(count > 0) {
                                errs()<<"Two paths from";
                                newPath.start.name->dump();
                                std::set<HOFGpath>::iterator pitl;
                                pathSet.insert(newPath);
                                pitl=pathSet.find(newPath);
                                //newPath=(*pitl);
                                addToPath(flowEdge,pitl);
                            }
                            count++;
                        }
                    }
                }
            }
        }
        void addToPath(F flowEdge,std::set<HOFGpath>::iterator psit) {
            (*psit).pathEdge.insert(flowEdge);
            int count =0;
            HOFGpath oldPath = (*psit);
            for(F edgeInGraph : HeapOFGraph.flows) {
                if(flowEdge.head == edgeInGraph.tail) {
                    if(count == 0) {
            //            oldPath = (*psit);
                        addToPath(edgeInGraph,psit);
                    } else {
                        oldPath.pathEdge.insert(edgeInGraph);
                        pathSet.insert(oldPath);
             //           if(pathSet.insert(oldPath).second) {
//
             //           } else {
             //               errs()<<"\n this is not happening";
             //           }
             //           psit=pathSet.find(oldPath);
             //           addToPath(edgeInGraph,psit);
                    }   
                    count++;
                }
            }
        }
        void generatePathHeads() {
            for(F edgeInGraph : HeapOFGraph.flows) {
                V vertex = edgeInGraph.tail;
                if(vertex.vertexTy == obj) {
                    HOFGpath p;
                    p.start = vertex;
                    //vertex.name->dump();
                    pathSet.insert(p);
                    //errs()<<"\npathHead added for path set count :"<<pathSet.size()<<"\n";
                }
            }
        }
        void detectResidueErrorType() {
            for(HOFGpath p : pathSet) {
                bool status = false;
                if(p.pathEdge.size() == 0) {
                    outs()<<"\nUnused allocation at: ";
                    unsigned loc = (dyn_cast<Instruction>(p.start.name))->getDebugLoc().getLine();
                    outs()<<"\nline number : "<<loc<<"\n";
                    const DebugLoc &location = (dyn_cast<Instruction>(p.start.name))->getDebugLoc();
                    //std::string dbgInfo;
                    //llvm::raw_string_ostream rso(dbgInfo);
                    //location->print(rso);
                    //std::string dbgStr = rso.str();
                    auto *Scope = cast<DIScope>(location->getScope());
                    std::string fileName = Scope->getFilename().str();
                    outs()<<"in file : "<<fileName<<"\n";
                } else {
                for(F f1 : p.pathEdge) {
                    status=false;
                    for(F f2 : p.pathEdge) {
                        if(f1.head == f2.tail) {
                            status=true;
                        }
                    }
                    if(!status) {
                        outs()<<"\nDangling pointer at";
                        //f1.head.name->dump();
                        //errs()<<"\n ....................";
                        unsigned loc = f1.location.getLine();
                        outs()<<"\n line number : "<<loc<<"\n";
                        //const DebugLoc &location = (dyn_cast<Instruction>(f1.head.name))->getDebugLoc();
                        //std::string dbgInfo;
                        //llvm::raw_string_ostream rso(dbgInfo);
                        //location->print(rso);
                        //std::string dbgStr = rso.str();
                        auto *Scope = cast<DIScope>(f1.location->getScope());
                        std::string fileName = Scope->getFilename().str();
                        outs()<<"in file : "<<fileName<<"\n";
                    }
                }
                }
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
                if(F.getName() == "xmalloc") {

                } else {
                    generateFunctionSummary(F);
                }
            }
        }
        void generateFunctionSummary(Function &F) { //generate HOFG of the function
                /*
                Function : constructHOFGfun(Function &F)
                Input : function
                Output : HOFG of the function
                */
                
                if(F.isDeclaration()) {

                } else if(F.getName() == "xmalloc"){

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
                //Following for loop is to record preds of bbs and conditions
                //errs()<<"\nGenerating preds and conditions for bbs of function"<<F.getName();
                for(Function::iterator FI=F.begin(); FI!=F.end(); FI++) {
                    BasicBlock &B(*FI);
                    predBB newPredSet;
                    newPredSet.bb=&B;
                    auto bt=pred_begin(&B);
                    auto et=pred_end(&B);
                    //errs()<<"\npreds conditions of BB "<<B.getName()<<" are\n";
                    for (bt = pred_begin(&B), et = pred_end(&B); bt != et; ++bt)
                    {
                        BasicBlock* predecessor = *bt;
                        Instruction* terminator = predecessor->getTerminator();
                        if(isa<BranchInst>(terminator)) {
                            BranchInst* br = dyn_cast<BranchInst>(terminator);
                            if(br->isConditional()) {
                                Value *cond= br->getCondition();
                            //    cond->dump();
                                for(BasicBlock* s : br->successors()) {
                                    if(s->getName() == B.getName()) {
                                        newPredSet.entriConditions.insert(cond);
                            //            errs()<<"Condition is for "<<s->getName()<<"\n";
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
                if(identifyBitCastCopy(I)) {
                    handleRelevantCodeSegment(GEP_BIT,B,I);
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
                            if(F->getName() == MALLOC|| F->getName() == "u_calloc" || F->getName() == "calloc") {
                                return true;
                            } else if (F->getName() ==  "xmalloc") {
                                //F->setName("malloc");
                                return true;
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
        bool identifyBitCastCopy(Instruction &I) {
            if(isa<BitCastInst>(I)) {
                if(isa<GetElementPtrInst>(I.getOperand(0))&&isa<PointerType>(I.getOperand(0)->getType())) {   
                    return true;
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
                if(isa<PointerType>(I.getOperand(0)->getType())) { 
                    return true;
                }
            }
            return false;
        }
        /*
        Function : annotateEdge (F flowEdge)
        Input : the flow edge of the HOFG
        Output : Annotate the flow edge with the conditions to be satisfied for the program to execute the statement represented by the edge.
        */
        void annotateEdge(F &flowEdge, Instruction &I) {
            //errs()<<"\nAnnotating edge : ";
            //flowEdge.tail.name->dump();
            //errs()<<"-->";
            //flowEdge.head.name->dump();
            BasicBlock *tail;
            //Conditions to be handled: 
            //global to global
            //global to arg
            //global to local
            //arg to global
            //arg to arg
            //arg to local
            //local to arg
            //local to global
            //local to local
            //if(isa<GlobalVariable>(flowEdge.tail.name)) {
              //  if(isa<GlobalVariable>(flowEdge.head.name)) { //global to global
             //       errs()<<"global to global";
                //} else if (isa<Argument>(flowEdge.head.name)){ 
             //   } 
             //   for(Argument &A : I.getFunction()->args()) {
              //          Value* arg = dyn_cast<Value>(&A);
             //           if(arg == flowEdge.head.name) {
                        //} else {
             //               break;
             //           }
             //       tail = dyn_cast<Instruction>(flowEdge.head.name)->getParent();
            //    }
            //} else if(isa<GlobalVariable>(flowEdge.head.name)) {
            //    if(isa<Argument>(flowEdge.tail.name)){
            //        tail = &(dyn_cast<Argument>(flowEdge.tail.name)->getParent()->getEntryBlock());
            //    } else {
            //        tail = dyn_cast<Instruction>(flowEdge.tail.name)->getParent();
            //    }
            //} else if(isa<Argument>(flowEdge.tail.name)){
                //tail = &(dyn_cast<Argument>(flowEdge.tail.name)->getParent()->getEntryBlock());
            //    tail = dyn_cast<Instruction>(flowEdge.head.name)->getParent();
            //}
            tail = I.getParent();
            
            predBB fromBB;
            fromBB.bb = tail;
            if(allBBs.find(fromBB) != allBBs.end()) {
                fromBB = *(allBBs.find(fromBB));
                //errs()<<"\nPrinting conditions";
                for (Value *c : fromBB.entriConditions) {
                 //   errs()<<"\n ";
                 //   c->dump();
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
                case GEP_BIT : addGepToBitcast(B,I);
                                break;
                default : errs()<<"\ninvalid instruction"<<option;
            }
        }
        void addMalloc(BasicBlock &B, Instruction &I) {
            errs()<<"\n Adding malloc into HOFG\n";
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
                    F flowEdge;
                    if(isa<BitCastInst>(Ins)) {//for two level pointers, there can be load statement instead of bitcast befor malloc
                        ptrNode.name=dyn_cast<Value>(&Ins);
                        ptrNode.vertexTy=ptr;
                        HeapOFGraph.vertices.insert(objNode);
                        HeapOFGraph.vertices.insert(ptrNode);
                        
                        flowEdge.head=ptrNode;
                        flowEdge.tail=objNode;
                        annotateEdge(flowEdge,I);
                        if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                        //    errs()<<"\nRepeat can be detected here";
                        } else if (isa<Argument>(ptrNode.name)) {
                            for(Argument &A : I.getFunction()->args()) {
                                Value* arg = dyn_cast<Value>(&A);
                                if(arg == ptrNode.name) {
                                    FuncSummary summary;
                                    summary.funcName = I.getFunction();
                                    if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                        fsit = allFuncSummaries.find(summary);
                                        annotateEdge(flowEdge,I);
                                        flowEdge.location=I.getDebugLoc();
                                        if(HeapOFGraph.flows.insert(flowEdge).second) {
                                            //annotateEdge(flowEdge,I);
                                            errs()<<"\n allocated from here";
                                            argTransformIt = fsit->argTransforms.begin();
                                            advance(argTransformIt,(dyn_cast<Argument>(arg))->getArgNo());
                                            fsit->argTransforms.insert(argTransformIt,allocator);
                                        }
                                    }
                                    annotateEdge(flowEdge,I);
                                    flowEdge.location=I.getDebugLoc();
                                    HeapOFGraph.flows.insert(flowEdge);
                                    break;
                                }
                            }            
                        } else if(isa<Argument>(Ins.getOperand(0))) {

                        } else {
                                //}
                            //}
                            annotateEdge(flowEdge,I);
                            flowEdge.location=I.getDebugLoc();
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
                        //errs()<<"\n In store";
                        ptrNode.vertexTy=ptr;
                        ptrNode.name=dyn_cast<Value>(Ins.getOperand(1));
                        HeapOFGraph.vertices.insert(objNode);
                        HeapOFGraph.vertices.insert(ptrNode);
                        
                        flowEdge.head=ptrNode;
                        flowEdge.tail=objNode;
                        
                        if(HeapOFGraph.vertices.find(ptrNode) != HeapOFGraph.vertices.end()) {
                            //errs()<<"\n Its already here ...";
                            //ptrNode.name->dump();
                            //Ins.getOperand(1)->dump();
                            if (isa<BitCastInst>(Ins.getOperand(1))) {
                                BitCastInst *bitc = dyn_cast<BitCastInst>(Ins.getOperand(1));
                                //errs()<<"\n reached here... have to handle it from here...";
                                if(isa<Argument>(bitc->getOperand(0))) {
                                    for(Argument &A : I.getFunction()->args()) {
                                        Value *arg = dyn_cast<Value>(&A);
                                        if(arg == bitc->getOperand(0)) {
                                            V argNode;
                                            std::set<V>::iterator vertit;
                                            argNode.name=arg;
                                            argNode.vertexTy=ptr;
                                            if(HeapOFGraph.vertices.find(argNode) != HeapOFGraph.vertices.end()) {
                                                vertit = HeapOFGraph.vertices.find(argNode);
                                            } else {
                                                HeapOFGraph.vertices.insert(argNode);
                                                vertit = HeapOFGraph.vertices.find(argNode);
                                            }
                                            F argFlowEdge;
                                            argFlowEdge.head=argNode;
                                            argFlowEdge.tail=ptrNode;
                                            annotateEdge(argFlowEdge,I);//Annotate should be double checked
                                            argFlowEdge.location = bitc->getDebugLoc();
                                            if(HeapOFGraph.flows.find(argFlowEdge) != HeapOFGraph.flows.end()) {
                                                errs()<<"\nEdge already there";
                                            } else {
                                                FuncSummary summary;
                                                summary.funcName = I.getFunction();
                                                std::set<FuncSummary>::iterator fsitloc;
                                                if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                                    fsitloc = allFuncSummaries.find(summary);
                                                    argTransformIt = fsitloc->argTransforms.begin();
                                                //errs()<<"\n its stuck here : \n"<< (dyn_cast<Argument>(arg))->getArgNo()<<"\n";
                                                    advance(argTransformIt,(dyn_cast<Argument>(arg))->getArgNo());
                                                    //errs()<<"\n adding dealloc at index 2: "<<(dyn_cast<Argument>(arg))->getArgNo()<<" for function : "<< I.getFunction()->getName();
                                                    fsitloc->functionType=allocator;
                                                    fsitloc->argTransforms.insert(argTransformIt,allocator);
                                                    errs()<<"\n lets see what happens here : "<<fsitloc->argTransforms.size();    
                                                }
                                                if(HeapOFGraph.flows.insert(argFlowEdge).second) {
                                                    errs()<<"\n Added edge";
                                                    argFlowEdge.tail.name->dump();
                                                    argFlowEdge.head.name->dump();
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            if (isa<Argument>(ptrNode.name)) {
                                for(Argument &A : I.getFunction()->args()) {
                                Value* arg = dyn_cast<Value>(&A);
                                if(arg == ptrNode.name) {
                                    FuncSummary summary;
                                    summary.funcName = I.getFunction();
                                    if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                        fsit = allFuncSummaries.find(summary);
                                        annotateEdge(flowEdge,I);
                                        flowEdge.location=I.getDebugLoc();
                                        if(HeapOFGraph.flows.insert(flowEdge).second) {
                                            //annotateEdge(flowEdge,I);
                                            errs()<<"\n Allocated from here 2";
                                            argTransformIt = fsit->argTransforms.begin();
                                            advance(argTransformIt,(dyn_cast<Argument>(arg))->getArgNo());
                                            fsit->argTransforms.insert(argTransformIt,allocator);
                                        }
                                    }
                                    annotateEdge(flowEdge,I);
                                    flowEdge.location=I.getDebugLoc();
                                    HeapOFGraph.flows.insert(flowEdge);
                                    break;
                                }
                                } 
                            
                            }
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
            //errs()<<"\nDEalloc statement found";
            V freeNode,ptrNode;
            freeNode.name=dyn_cast<Value>(&I);
            freeNode.vertexTy=snk;
            if (HeapOFGraph.vertices.find(freeNode) != HeapOFGraph.vertices.end()) {
                //errs()<<"\nfree node found";
                vit=HeapOFGraph.vertices.find(freeNode);
                freeNode = *vit;
                //freeNode.name->dump();
            } else {
                //if(! (HeapOFGraph.vertices.insert(freeNode).second)) {
                    //errs()<<"\nHere is the real culprit";
                //}
            }
            if (isa<Argument>(I.getOperand(0))) {
                for(Argument &A : I.getFunction()->args()) {
                    Value* arg = dyn_cast<Value>(&A);
                    if(arg == I.getOperand(0)) {
                        ptrNode.name=dyn_cast<Value>(I.getOperand(0));
                        if (HeapOFGraph.vertices.find(ptrNode) != HeapOFGraph.vertices.end()) {
                            ptrNode=*(HeapOFGraph.vertices.find(ptrNode));
                            F flowEdge;
                            flowEdge.tail=ptrNode;
                            flowEdge.head=freeNode;
                            HeapOFGraph.vertices.insert(freeNode);
                            annotateEdge(flowEdge,I);
                            flowEdge.location=I.getDebugLoc();
                            if(HeapOFGraph.flows.insert(flowEdge).second) {
                                FuncSummary summary;
                                summary.funcName = I.getFunction();
                                if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                    fsit = allFuncSummaries.find(summary);
                                    //fsit->argTransforms.push_back(deallocator);
                                    argTransformIt = fsit->argTransforms.begin();
                                    advance(argTransformIt,(dyn_cast<Argument>(arg))->getArgNo());
                                    //errs()<<"\n adding dealloc at index 1: "<<(dyn_cast<Argument>(arg))->getArgNo()<<" for function : "<< I.getFunction()->getName();
                                    if(*argTransformIt == deallocator) {

                                    } else {
                                        fsit->argTransforms.insert(argTransformIt,deallocator);
                                    }                                
                                }
                            }
                        }
                        break;
                    }
                }
            }
            for(BasicBlock::iterator BI=B.begin(); BI!=B.end(); BI++) {
                Instruction &Ins(*BI);
                if(dyn_cast<Instruction>(I.getOperand(0)) == &Ins) {
                    if(isa<BitCastInst>(Ins) && isa<LoadInst>(Ins.getOperand(0))) {
                        LoadInst *load = dyn_cast<LoadInst>(Ins.getOperand(0));
                        if(isa<PointerType>(load->getType())) {
                            if(GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(load->getOperand(0))) {
                                if(isa<Argument>(gep->getOperand(0))){ //|| isa<Argument>(dyn_cast<Instruction>(ptrNode.name)->getOperand(0))) {
                                    //errs()<<"\ntail is an arg\n";
                                    //errs()<<"\n ..... \n";
                                    for(Argument &A : I.getFunction()->args()) {
                                        //errs()<<"\n ...... \n";
                                        Value* arg = dyn_cast<Value>(&A);
                                        if(arg == gep->getOperand(0)) {
                                            std::set<V>::iterator vertit;
                                            freeNode.name=dyn_cast<Value>(&I);
                                            freeNode.vertexTy=snk;
                                            if(HeapOFGraph.vertices.find(freeNode) != HeapOFGraph.vertices.end()) {
                                                vertit=HeapOFGraph.vertices.find(freeNode);
                                            } else {
                                                if(HeapOFGraph.vertices.insert(freeNode).second) {
                                                    vertit=HeapOFGraph.vertices.find(freeNode);
                                                }
                                            }
                                            ptrNode.name = gep->getOperand(0);
                                            ptrNode.vertexTy = ptr;
                                            if(HeapOFGraph.vertices.find(freeNode) != HeapOFGraph.vertices.end()) {
                                               
                                            } else {
                                                if(HeapOFGraph.vertices.insert(freeNode).second) {
                                                    
                                                }
                                            }
                                            F flowEdge;
                                            flowEdge.tail=ptrNode;
                                            flowEdge.head=freeNode;
                                            annotateEdge(flowEdge,I);
                                            flowEdge.location=I.getDebugLoc();
                                            if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                                            //    errs()<<"\nRepeat can be detected here";
                                            } else {
                                                if(HeapOFGraph.flows.insert(flowEdge).second){
                                                    //errs()<<"\nEdge added";
                                                    FuncSummary summary;
                                                    summary.funcName = I.getFunction();
                                                    if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                                        std::set<FuncSummary>::iterator fsitl;
                                                        std::list<funcType>::iterator argTransformItl;
                                                        fsitl = allFuncSummaries.find(summary);
                                                        //errs()<<"\n in here"<<fsitl->funcName->getName();
                                                        //errs()<<fsitl->argTransforms.size()<<"\n";
                                                        argTransformItl = fsitl->argTransforms.begin();
                                                        //advance(argTransformItl,(dyn_cast<Argument>(arg))->getArgNo());
                                                        if(find(fsitl->argTransforms.begin(),fsitl->argTransforms.end(),deallocator) != fsitl->argTransforms.end()) {
                                                            fsitl->functionType=deallocator;
                                                         //   errs()<<"and here!!!!!!!!!!";
                                                        //    errs()<<"\nthe function "<<I.getFunction()->getName()<<" is a n allocator";
                                                        //    errs()<<fsitl->argTransforms.size()<<"\n";
                                                        } else {
                                                         //   errs()<<"safely here............";
                                                            fsitl->argTransforms.insert(argTransformItl,deallocator);
                                                        //    fsit->functionType=allocator;
                                                        //    errs()<<"\nthe function "<<I.getFunction()->getName()<<" is an allocator1";
                                                        }
                                                        //*argTransformItl=allocator;
                                                        //fsit->argTransforms.push_back(allocator);
                                                        fsitl->functionType=deallocator;
                                                        //errs()<<"............................................."<<fsitl->argTransforms.size()<<"\n";
                                                        if(fsitl->functionType == deallocator){
                                                            //errs()<<"\n deallocator marked";
                                                        }
                                                    }
                                                }
                                            }

                                        }
                                    }
                                }
                            }
                        }
                    //} else if(isa<BitCastInst>(Ins) && isa<GetElementPtrInst>(Ins.getOperand(0))) {
                    //    GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(Ins.getOperand(0));
                    //    //if(load->getType()) {
                    //        if(LoadInst *load = dyn_cast<LoadInst>(gep->getOperand(0))) {
                    //            if(isa<Argument>(load->getOperand(0))){ //|| isa<Argument>(dyn_cast<Instruction>(ptrNode.name)->getOperand(0))) {
                    //                //errs()<<"\ntail is an arg\n";
                    //                //errs()<<"\n ..... \n";
                    //                for(Argument &A : I.getFunction()->args()) {
                    //                    //errs()<<"\n ...... \n";
                    //                    Value* arg = dyn_cast<Value>(&A);
                    //                    if(arg == load->getOperand(0)) {
                    //                        std::set<V>::iterator vertit;
                    //                        freeNode.name=dyn_cast<Value>(&I);
                    //                        freeNode.vertexTy=snk;
                    //                        if(HeapOFGraph.vertices.find(freeNode) != HeapOFGraph.vertices.end()) {
                    //                            vertit=HeapOFGraph.vertices.find(freeNode);
                    //                        } else {
                    //                            if(HeapOFGraph.vertices.insert(freeNode).second) {
                    //                                vertit=HeapOFGraph.vertices.find(freeNode);
                    //                            }
                    //                        }
                    //                        ptrNode.name = load->getOperand(0);
                    //                        ptrNode.vertexTy = ptr;
                    //                        if(HeapOFGraph.vertices.find(freeNode) != HeapOFGraph.vertices.end()) {
                    //                           
                    //                        } else {
                    //                            if(HeapOFGraph.vertices.insert(freeNode).second) {
                    //                                
                    //                            }
                    //                        }
                    //                        F flowEdge;
                    //                        flowEdge.tail=ptrNode;
                    //                        flowEdge.head=freeNode;
                    //                        annotateEdge(flowEdge,I);
                    //                        flowEdge.location=I.getDebugLoc();
                    //                        if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                    //                        //    errs()<<"\nRepeat can be detected here";
                    //                        } else {
                    //                            if(HeapOFGraph.flows.insert(flowEdge).second){
                    //                                //errs()<<"\nEdge added";
                    //                                FuncSummary summary;
                    //                                summary.funcName = I.getFunction();
                    //                                if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                    //                                    std::set<FuncSummary>::iterator fsitl;
                    //                                    std::list<funcType>::iterator argTransformItl;
                    //                                    fsitl = allFuncSummaries.find(summary);
                    //                                    //errs()<<"\n in here"<<fsitl->funcName->getName();
                    //                                    //errs()<<fsitl->argTransforms.size()<<"\n";
                    //                                    argTransformItl = fsitl->argTransforms.begin();
                    //                                    //advance(argTransformItl,(dyn_cast<Argument>(arg))->getArgNo());
                    //                                    if(find(fsitl->argTransforms.begin(),fsitl->argTransforms.end(),deallocator) != fsitl->argTransforms.end()) {
                    //                                        fsitl->functionType=deallocator;
                    //                                     //   errs()<<"and here!!!!!!!!!!";
                    //                                    //    errs()<<"\nthe function "<<I.getFunction()->getName()<<" is a n allocator";
                    //                                    //    errs()<<fsitl->argTransforms.size()<<"\n";
                    //                                    } else {
                    //                                     //   errs()<<"safely here............";
                    //                                        fsitl->argTransforms.insert(argTransformItl,deallocator);
                    //                                    //    fsit->functionType=allocator;
                    //                                    //    errs()<<"\nthe function "<<I.getFunction()->getName()<<" is an allocator1";
                    //                                    }
                    //                                    //*argTransformItl=allocator;
                    //                                    //fsit->argTransforms.push_back(allocator);
                    //                                    fsitl->functionType=deallocator;
                    //                                    //errs()<<"............................................."<<fsitl->argTransforms.size()<<"\n";
                    //                                    if(fsitl->functionType == deallocator){
                    //                                        //errs()<<"\n deallocator marked";
                    //                                    }
                    //                                }
                    //                            }
                    //                        }
//
                    //                    }
                    //                }
                    //            }
                    //        }
                    //    //}
                    } else if(isa<BitCastInst>(Ins)) {//for 2 level pointers, there can be load instead of bitcast as operand of free
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
                            } else {
                                //errs()<<"\nIt is added freom here";
                            }
                        }
                        F flowEdge;
                        flowEdge.tail=ptrNode;
                        flowEdge.head=freeNode;
                        //if (! (HeapOFGraph.flows.insert(flowEdge).second)) { .insert.second will return if the insertion is successful
                            //errs()<<"Here it didnt work";
                        //}
                        annotateEdge(flowEdge,I);
                        if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                        //    errs()<<"\nRepeat can be detected here";
                        } else {
                            //for(Argument &A : I.getFunction()->args()) {
                            //    Value* arg = dyn_cast<Value>(&A);
                                //arg->dump();
                                //ptrNode.name->dump();
                            //errs()<<"\n adding new edge";
                            HeapOFGraph.vertices.insert(freeNode);
                            annotateEdge(flowEdge,I);
                            flowEdge.location=I.getDebugLoc();
                            if(HeapOFGraph.flows.insert(flowEdge).second){

                                if(isa<Argument>(ptrNode.name)){ //|| isa<Argument>(dyn_cast<Instruction>(ptrNode.name)->getOperand(0))) {
                                    //errs()<<"\ntail is an arg\n";
                                    //errs()<<"\n ..... \n";
                                    for(Argument &A : I.getFunction()->args()) {
                                        //errs()<<"\n ...... \n";
                                        Value* arg = dyn_cast<Value>(&A);
                                        if(arg == ptrNode.name || arg == dyn_cast<Instruction>(ptrNode.name)->getOperand(0)) {
                                            //errs()<<"\n ........... \n";
                                            Argument *arg = dyn_cast<Argument>(ptrNode.name);
                                            FuncSummary summary;
                                            summary.funcName = I.getFunction();
                                            if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                                fsit = allFuncSummaries.find(summary);
                                                //errs()<<"\n ......;..........\n";
                                                //fsit->argTransforms.push_back(deallocator);
                                                argTransformIt = fsit->argTransforms.begin();
                                                //errs()<<"\n its stuck here : \n"<< (dyn_cast<Argument>(arg))->getArgNo()<<"\n";
                                                    advance(argTransformIt,(dyn_cast<Argument>(arg))->getArgNo());
                                                    //errs()<<"\n adding dealloc at index 2: "<<(dyn_cast<Argument>(arg))->getArgNo()<<" for function : "<< I.getFunction()->getName();
                                    
                                                    fsit->argTransforms.insert(argTransformIt,deallocator);
                                                //fsit->functionType=allocator;
                                            }
                                            break;
                                        }
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
                            }
                            //}
                            
                        }
                        //errs()<<"\n Adding flow edge while handling dealloc : \n";
                        //Ins.dump();
                        //errs()<<"\n to \n";
                        //I.dump();
                        //errs()<<"...................";
                    } else if (isa<LoadInst>(Ins) && isa<PointerType>(Ins.getType())) {
                        //errs()<<"\n here it comes";
                        ptrNode.name=dyn_cast<Value>(&Ins);
                        if (HeapOFGraph.vertices.find(ptrNode) != HeapOFGraph.vertices.end()) {
                            ptrNode=*(HeapOFGraph.vertices.find(ptrNode));
                            F flowEdge;
                            flowEdge.tail=ptrNode;
                            flowEdge.head=freeNode;
                            HeapOFGraph.vertices.insert(freeNode);
                            annotateEdge(flowEdge,I); 
                            flowEdge.location=I.getDebugLoc();
                            HeapOFGraph.flows.insert(flowEdge);
                        }
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
                            annotateEdge(flowEdge,I); 
                            flowEdge.location=I.getDebugLoc();
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
                annotateEdge(flowEdge,I);
                if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                        //    errs()<<"\nRepeat can be detected here";
                        } else {
                            //for(Argument &A : I.getFunction()->args()) {
                            //    Value* arg = dyn_cast<Value>(&A);
                                if(isa<Argument>(destNode.name)) {
                                    for(Argument &A : I.getFunction()->args()) {
                                        Value* arg = dyn_cast<Value>(&A);
                                        if(arg == destNode.name) {
                                        //errs()<<"\nhead is an arg in copy\n";
                                            FuncSummary summary;
                                            summary.funcName = I.getFunction();
                                            if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                                fsit = allFuncSummaries.find(summary);
                                                //fsit->argTransforms.push_back(allocator);
                                                //fsit->functionType=allocator;
                                                argTransformIt = fsit->argTransforms.begin();
                                                advance(argTransformIt,(dyn_cast<Argument>(arg))->getArgNo());
                                                //errs()<<"\n adding dealloc at index 3: "<<(dyn_cast<Argument>(arg))->getArgNo()<<" for function : "<< I.getFunction()->getName();
                                    
                                                fsit->argTransforms.insert(argTransformIt,deallocator);
                                            }
                                            break;
                                        }
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
                                annotateEdge(flowEdge,I);
                            }
                            flowEdge.location=I.getDebugLoc();
                            HeapOFGraph.flows.insert(flowEdge);
                        }
            } else {
                //errs()<<"\n Found as not an exising vertex!!!";
                //I.dump();
            }
        }
        void addGepToBitcast(BasicBlock &B, Instruction &I) {
            //errs()<<"\nIn this function";
            //errs()<<I.getFunction()->getName();
            V srcNode, destNode;
            std::set<V>::iterator dit;
            srcNode.name=dyn_cast<Value>(&I);
            //I.getOperand(0)->dump();
            srcNode.vertexTy=ptr;
            if(HeapOFGraph.vertices.find(srcNode) != HeapOFGraph.vertices.end()) {
                GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(I.getOperand(0));
                //errs()<<"\nGoing to add : ";
                //I.dump();
                vit=HeapOFGraph.vertices.find(srcNode);
                srcNode = *vit;
                destNode.name=dyn_cast<Value>(gep->getOperand(0));
                //gep->getOperand(0)->dump();
                destNode.vertexTy=ptr;
                if(HeapOFGraph.vertices.find(destNode) != HeapOFGraph.vertices.end()) {
                    //errs()<<"\n existing dest";
                    dit = HeapOFGraph.vertices.find(destNode);
                    destNode = *dit;
                    //errs()<<"\n inserting ";
                    //destNode.name->dump();
                } else {
                    //errs()<<"\nnew dest";
                    HeapOFGraph.vertices.insert(destNode);
                    dit = HeapOFGraph.vertices.find(destNode);
                    destNode = *dit;
                }
                F flowEdge;
                flowEdge.head=destNode;
                flowEdge.tail=srcNode;
                annotateEdge(flowEdge,I);
                if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                //    errs()<<"\nRepeat can be detected here";
                } else {
                    if(isa<Argument>(destNode.name)) {
                        for(Argument &A : I.getFunction()->args()) {
                            //errs()<<"\n in arg loop";
                            Value* arg = dyn_cast<Value>(&A);
                            if(arg == destNode.name) {
                               // errs()<<"\n arg is dest node name";
                                FuncSummary summary;
                                summary.funcName = I.getFunction();
                                if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                    std::set<FuncSummary>::iterator fsitl;
                                    std::list<funcType>::iterator argTransformItl;
                                    fsitl = allFuncSummaries.find(summary);
                                 //   errs()<<"\n in here"<<fsitl->funcName->getName();
                                   // errs()<<fsitl->argTransforms.size()<<"\n";
                                    argTransformItl = fsitl->argTransforms.begin();
                                    //advance(argTransformItl,(dyn_cast<Argument>(arg))->getArgNo());
                                    if(find(fsitl->argTransforms.begin(),fsitl->argTransforms.end(),allocator) != fsitl->argTransforms.end()) {
                                        fsitl->functionType=allocator;
                                     //   errs()<<"and here!!!!!!!!!!";
                                    //    errs()<<"\nthe function "<<I.getFunction()->getName()<<" is a n allocator";
                                    //    errs()<<fsitl->argTransforms.size()<<"\n";
                                    } else {
                                     //   errs()<<"safely here............";
                                        fsitl->argTransforms.insert(argTransformItl,allocator);
                                    //    fsit->functionType=allocator;
                                    //    errs()<<"\nthe function "<<I.getFunction()->getName()<<" is an allocator1";
                                    }
                                    //*argTransformItl=allocator;
                                    //fsit->argTransforms.push_back(allocator);
                                    fsitl->functionType=allocator;
                                    //errs()<<"............................................."<<fsitl->argTransforms.size()<<"\n";
                                    if(fsitl->functionType == allocator){
                                    //    errs()<<"\n allocator marked";
                                    }
                                }
                                break;
                            }
                        }
                    }
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
                        annotateEdge(flowEdge,I);
                    }
                    flowEdge.location=I.getDebugLoc();
                    HeapOFGraph.flows.insert(flowEdge);
                }
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
                srcNode.vertexTy=ptr;
                if(HeapOFGraph.vertices.find(srcNode) != HeapOFGraph.vertices.end()) {
                    //errs()<<"\n Found an existing node !!! \n";
                    srcNode=*(HeapOFGraph.vertices.find(srcNode));
                    if(HeapOFGraph.vertices.find(destNode) != HeapOFGraph.vertices.end()) {
                    //This is a copy to existing node.
                        vit=HeapOFGraph.vertices.find(destNode);
                        destNode = *vit;
                    } else {
                        HeapOFGraph.vertices.insert(destNode);
                    }
                    F flowEdge;
                    flowEdge.head=destNode;
                    flowEdge.tail=srcNode;
                    F circularEdge;
                    circularEdge.head=srcNode;
                    circularEdge.tail=destNode;
                    annotateEdge(circularEdge,I);
                    //flowEdge.condition=src;
                    annotateEdge(flowEdge,I);
                    if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                        //    errs()<<"\nRepeat can be detected here";
                    } else if (HeapOFGraph.flows.find(circularEdge) != HeapOFGraph.flows.end()) {
                    } else {
                        //for(Argument &A : I.getFunction()->args()) {
                        //    Value* arg = dyn_cast<Value>(&A);
                        if(isa<Argument>(destNode.name)) {
                            for(Argument &A : I.getFunction()->args()) {
                                Value* arg = dyn_cast<Value>(&A);
                                if(arg == destNode.name) {
                                    //errs()<<"\nhead is an arg in phi\n";
                                    FuncSummary summary;
                                    summary.funcName = I.getFunction();
                                    if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                                        fsit = allFuncSummaries.find(summary);
                                        //fsit->argTransforms.push_back(allocator);
                                        //fsit->functionType=allocator;
                                        argTransformIt = fsit->argTransforms.begin();
                                        advance(argTransformIt,(dyn_cast<Argument>(arg))->getArgNo());
                                        //errs()<<"\n adding dealloc at index 4: "<<(dyn_cast<Argument>(arg))->getArgNo()<<" for function : "<< I.getFunction()->getName();
                            
                                        fsit->argTransforms.insert(argTransformIt,deallocator);
                                    }
                                    break;
                                }
                            }
                        }
                            //if(isa<Argument>(srcNode.name)) {
                            //    for(Argument &A : I.getFunction()->args()) {
                            //        Value* arg = dyn_cast<Value>(&A);
                            //        if(arg == srcNode.name) {
                                //srcNode.name->dump();
                                //destNode.name->dump();
                                       // errs()<<"\nSource of phi instruction is an argument";
                                        //break;
                            //        }
                            //    }
                            //}
                        //}
                        annotateEdge(flowEdge,I);
                        flowEdge.location=I.getDebugLoc();
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
                annotateEdge(flowEdge,I);
                if(HeapOFGraph.flows.find(flowEdge) != HeapOFGraph.flows.end()) {
                //    errs()<<"\nRepeat can be detected here";
                } else {
                    FuncSummary summary;
                    //errs()<<"\n this is happening : for function "<<I.getFunction()->getName()<<"\n";
                    //for(Argument &A : I.getFunction()->args()) {
                    //    Value* arg = dyn_cast<Value>(&A);
                    //    if(arg == destNode.name) {
                    //        errs()<<"\n it comes here and does: \n";
                    ////if(isa<Argument>(destNode.name)) {
                    //   // errs()<<"\nhead is an arg in store\n";
                    //    summary.funcName = I.getFunction();
                    //    if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                    //        fsit = allFuncSummaries.find(summary);
                    //    //    fsit->argTransforms.push_back(allocator);
                    //    //    errs()<<fsit->argTransforms.size()<<"size\n";
                    //        argTransformIt = fsit->argTransforms.begin();
                    //        errs()<<"The index of arg transform 4: "<<dyn_cast<Argument>(arg)->getArgNo()<<"\n";
                    //        advance(argTransformIt,(dyn_cast<Argument>(arg))->getArgNo());
                    //        fsit->argTransforms.insert(argTransformIt,deallocator);
                    //    }
                    //    break;
                    //}
                    //}
                    if(isa<GlobalVariable>(destNode.name)) {
                        summary.funcName = I.getFunction();
                        if(allFuncSummaries.find(summary)!=allFuncSummaries.end()) {
                            fsit = allFuncSummaries.find(summary);
                            //Value *v = dyn_cast<Value>(storIns->getOperand(1));
                            fsit->globalAlloc.insert(dyn_cast<Value>(storIns));
                            //errs()<<"\nglobal value allocated for function : "<<I.getFunction()->getName();
                        }
                    }
                    //if(isa<Argument>(srcNode.name)) {
                    for(Argument &A : I.getFunction()->args()) {
                        Value* arg = dyn_cast<Value>(&A);
                        if(arg == srcNode.name) {
                        //errs()<<"\n source node of store is argument";
                        break;
                    }
                    }
                    //    }
                    //}
                    //errs()<<fsit->argTransforms.size()<<"size\n";
                    annotateEdge(flowEdge,I);
                    flowEdge.location=I.getDebugLoc();
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
                            annotateEdge(flowEdge,I);
                            flowEdge.location=I.getDebugLoc();
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
            //errs()<<"\nIn apply summary of the function for call: ";
            //I.dump();
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
                        //    errs()<<"\n Allocator of arg detected in function type allocator";
                            //To do: add edge from formal arg to actual arg
                        } else if (t==deallocator) {
                        //    errs()<<"\nDeallocator of arg detected in function type allocator";
                        } else if (t==noop) {
                        //    errs()<<"\nnoop of arg detected in function type allocator";
                        }
                    }
                //}
            }
            if(summary.argTransforms.size() > 0) {
                //errs()<<"\nIn apply summary of the function for call: ";
                //I.dump();
                //errs()<<"\nArg transforms detected\n";
                for(funcType t: summary.argTransforms) {
                    if (t==deallocator) {
                    //    errs()<<"\nDeallocator detected for args in "<<summary.funcName->getName();
                        addDeallocArg(summary,I);
                    } else if (t==allocator) {
                        addAllocArg(summary,I);
                    }
                }
            }
            if(summary.globalAlloc.size() > 0) {
                addGlobalAlloc(summary.globalAlloc,I);
            //    errs()<<"\nglobal value is allocated";
            }
            if(summary.globalDealloc.size() > 0) {
                addGlobalDealloc(summary.globalDealloc,I);
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
            annotateEdge(flowEdge,I);
            flowEdge.location=I.getDebugLoc();
            HeapOFGraph.flows.insert(flowEdge);
        }
        void addGlobalDealloc(std::set<Value*> deallocSet, Instruction &I) {
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
                annotateEdge(flowEdge,I);
                flowEdge.location=I.getDebugLoc();
                HeapOFGraph.flows.insert(flowEdge);
            }
        }
        void addGlobalAlloc(std::set<Value*> allocSet, Instruction &I) {
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
                        ptrNode.name=dyn_cast<Value>(bcI);
                        if(HeapOFGraph.vertices.find(ptrNode) != HeapOFGraph.vertices.end()) {
                            ptrNode=*(HeapOFGraph.vertices.find(ptrNode));
                        }
                        flowEdge1.tail=objNode;
                        flowEdge1.head=ptrNode;
                        annotateEdge(flowEdge1,I);
                        flowEdge1.location=I.getDebugLoc();
                        HeapOFGraph.flows.insert(flowEdge1);
                        flowEdge2.tail=ptrNode;
                        flowEdge2.head=globalNode;
                        annotateEdge(flowEdge2,I);
                        flowEdge2.location=I.getDebugLoc();
                        HeapOFGraph.flows.insert(flowEdge2);
                    }
                }
            }
        }
        void addDeallocArg(FuncSummary summary, Instruction &I) {
            //errs()<<"\n Adding dealloc of summary";
            int argNumber=0;
            CallInst *call=dyn_cast<CallInst>(&I);
            Function *calledFunction = dyn_cast<Function>(call->getCalledFunction());
            for(funcType t: summary.argTransforms) {
                
                if (t==deallocator) {
                //    errs()<<"\nDeallocator edges to be added for "<<summary.funcName->getName();
                    for (Value *A : call->args()) {
                        //errs()<<"\n the arg that is going to be deallocated is : ";
                        //A->dump();
                        V argNode,ptrNode;
                        F flowEdge;
                        argNode.name=A;
                        argNode.vertexTy=ptr;
                        if(HeapOFGraph.vertices.find(argNode) != HeapOFGraph.vertices.end()) {
                            argNode=*(HeapOFGraph.vertices.find(argNode));
                        }
                        //errs()<<"......\n";
                        //errs()<<summary.argTransforms.size()<<"\n";
                        //errs()<<"call->args and calledFunction->args size : and arg size is : " << argNumber<<"\n";
                        //call->dump();
                        //errs()<<"\n....\n";
                        //calledFunction->dump();
                        //errs()<<"\n.......\n";
                        //errs()<<call->args().size()<<".....and ...."<<calledFunction->args().size();
                        //errs()<<"\nSo an edge is to be added from this to ";
                        Argument *formalArg = calledFunction->getArg(argNumber);
                        //formalArg->dump();
                        ptrNode.name=dyn_cast<Value>(formalArg);
                        ptrNode.vertexTy=ptr;
                        flowEdge.head=ptrNode;
                        flowEdge.tail=argNode;
                        annotateEdge(flowEdge,I);
                        flowEdge.location=I.getDebugLoc();
                        HeapOFGraph.flows.insert(flowEdge);
                    }
                }
                argNumber++;
            }
        }
        void addAllocArg(FuncSummary summary, Instruction &I) {
            int argNumber=0;
            CallInst *call=dyn_cast<CallInst>(&I);
            Function *calledFunction = dyn_cast<Function>(call->getCalledFunction());
            for(funcType t: summary.argTransforms) {
                //errs()<<"\n here for :";
                //I.dump();
                //errs()<<"\n ..........................";
                if (t==allocator) {
                //    errs()<<"\nDeallocator edges to be added for "<<summary.funcName->getName();
                    for (Value *A : call->args()) {
                        V argNode,ptrNode;
                        F flowEdge;
                        argNode.name=A;
                        argNode.vertexTy=ptr;
                        //errs()<<"\n the arg that is going to be allocated is : ";
                        //A->dump();
                        if(HeapOFGraph.vertices.find(argNode) != HeapOFGraph.vertices.end()) {
                            argNode=*(HeapOFGraph.vertices.find(argNode));
                        }
                        //errs()<<"......\n";
                        //errs()<<"\nSo an edge is to be added to this from ";
                        Argument *formalArg = calledFunction->getArg(argNumber);
                        //formalArg->dump();
                        ptrNode.name=dyn_cast<Value>(formalArg);
                        ptrNode.vertexTy=ptr;
                        flowEdge.tail=ptrNode;
                        flowEdge.head=argNode;
                        annotateEdge(flowEdge,I);
                        flowEdge.location=I.getDebugLoc();
                        HeapOFGraph.flows.insert(flowEdge);
                    }
                }
                argNumber++;
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


