#include <map>
#include <vector>
#include <deque>
#include <list>
#include <iostream>
#include <fstream>
#include <dirent.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <errno.h>

#include "AllPasses.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/TypeFinder.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Bitcode/ReaderWriter.h"

#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"

#include "Config.h"
#include "ConnectFunctions.h"
#include "FunctionWrapper.h"
#include "ProgramDependencies.h"
#include "SystemDataDependencies.h"
#include "SystemControlDependenceGraph.h"
#include "GetCallGraph.h"

using namespace std;
using namespace cot;
using namespace llvm;


class MemberType {
public:
  Type* ty;
  int complexity;
  int level; // root 0
  Type* parentTy;
  // children getContainedTypes....
  vector<MemberType> children;

  MemberType(Type* _ty, Type* _parentTy, 
	     int _level, int _complexity,
	     vector<MemberType> vec){
    ty = _ty;
    parentTy = _parentTy;
    level = _level;
    complexity = _complexity;
    children = vec;
  }
  ~MemberType();
};





/*
    for (int i = 0; i < ty->getNumContainedTypes(); i++){
      children
    }
*/

class CallPair {
public:
  string caller;
  string callee;

  CallPair(string _caller, string _callee){
    caller = _caller;
    callee = _callee;
  }
  bool operator==(const CallPair &other) const{
    return (caller == other.caller) && (callee == other.callee);
  }
};

class CallEdge{
public:
  string caller;
  string callee;
  int call_times;
  float type_complexity;
  int param_leak;
  int return_leak;

  CallEdge(string _caller, string _callee, int _call_times, float _type_complexity){
    caller = _caller;
    callee = _callee;
    call_times = _call_times;
    type_complexity = _type_complexity;
    param_leak = 0;
    return_leak = 0; 
  }
};

class CallEdgeWithGlobal{
public:
  string caller;
  string callee;
  int call_times;
  float type_complexity;
  int param_leak;
  int return_leak;

  CallEdgeWithGlobal(string _caller, string _callee, int _call_times, float _type_complexity){
    caller = _caller;
    callee = _callee;
    call_times = _call_times;
    type_complexity = _type_complexity;
    param_leak = 0;
    return_leak = 0; 
  }
};


extern std::set<FunctionWrapper*> sen_FuncSet;
extern std::set<FunctionWrapper*> ins_FuncSet;

extern vector<pair<string, string> > edgesWithParamLeak;
extern vector<pair<string, string> > edgesWithReturnLeak;

static unsigned int call_site_id = 0;

set<CallSiteWrapper*> cswSet;
set<CallSiteWrapper*> cswSetFromFile;

vector<CallPair> callPairsFromPin;

vector<CallEdge> CG; // static call graph
vector<CallEdge> GlobalCG; // static call graph, only for global variables

set<string> funcSet;
map<string, int> funcDict;
set<FidSize*> fidSizeSet;
set<FidSize*> fidSizeSetForGlobals; // for globals

// string: global name, int: id
map<string, int> globalDict;

static set<string> existedFiles;



int NumFields = 0;
set<Type*> recursiveTypes; //Struct only
static map<Type*, int> StructTyMap;

static map<Type*, int> typeCache;



Type* getNonPointerBaseTy(Type* ty){
  while (ty->isPointerTy()){
    ty = ty->getContainedType(0);
  }
  return ty;
}



//E.g. %struct.TimerStruct = type { void (i8*, %struct.timeval*)*, %union.ClientData, 
// i64, i32, %struct.timeval, %struct.TimerStruct*, %struct.TimerStruct*, i32 }
int evaluateStructTy(Type* STy){
  if (STy == nullptr){
    errs() << "evaluateSturctTy, STy is nullptr!\n";
    exit(1);
  }
  errs() << "STy: " << *STy << "------------------\n";
  if (typeCache.find(STy) != typeCache.end()){
    errs() << "STy is in typeCache, typeCache.size: " << typeCache.size() << "\n";
    return typeCache[STy];
  }

  int max = 0; 
  for (int i = 0; i < STy->getStructNumElements(); i++){
    int elem = 0;
    Type* ty = STy->getStructElementType(i);
    
    errs() << i << " ElemTy: " << *ty << "\n";
    if (ty->isPointerTy()){
      Type* pteTy = ty->getContainedType(0);
      errs() << "pteTy: " << *pteTy << " ------ ";
      // check the pointee type, if struct, check existedTypes
      // if existed, stop and return 1, otherwise, evaluate it
      if (pteTy->isStructTy()){
	if (recursiveTypes.find(pteTy) != recursiveTypes.end())
	  elem = 1;
	else{
	  errs() << "not in recursiveTypes\n";
	  elem = evaluateStructTy(pteTy);
	  
	}
      }
      else if (pteTy->isFunctionTy())
	elem = 1;
      // only for multiple level pointers with no struct in the middle
      else if (pteTy->isPointerTy()){
	while (pteTy->isPointerTy()){
	  elem++;
	  pteTy = pteTy->getContainedType(0);
	}
      }
      else elem = 0; // default
    }
    else if (ty->isStructTy()){
      errs() << " (case 2: structTy) ";
      elem = evaluateStructTy(ty);
    }
    else
      elem = 0;

    errs() << "elem = " << elem << "\n";
    max = (max >= elem) ? max : elem;
  }

  // store STy's type complexity in the cache
  if (typeCache.find(STy) == typeCache.end()){
    typeCache[STy] = max;
    errs() << "Cache ty = " << *STy << " complexity: " << max << "\n";
  }
  return max;
}


bool isInt8PointerTy(Type* ty){
  if(PointerType *PT = dyn_cast<PointerType>(ty))
    if (IntegerType *IT = dyn_cast<IntegerType>(PT->getPointerElementType()))
      if (IT->getBitWidth() == 8)
	return true;

  return false;
}

int getComplexity(Type* ty){
  if (ty == nullptr) return 0;

  if(ty->isStructTy()){
    //    errs() << "StructTy: " << *ty << "\n";
    return StructTyMap[ty];
  }
  // take care of recursive types. e.g. linked list
  if (ty->isPointerTy()){

    // if i8* (char*)
    //    if (isInt8PointerTy(ty->getContainedType(0)))
    //  return 1;

    if (ty->getContainedType(0)->isFunctionTy()){
      errs() << "FunctionTy found\n";
      errs() << *ty->getContainedType(0) << "\n";
      return 1;
    }
    return 1 + getComplexity(ty->getContainedType(0));
  }

  // TODO: is 1 OK for FunctionTy?
  if (ty->isFunctionTy()){
    errs() << "ty is FunctionTy: " << *ty << "\n";
    return 1;
  }
  // we consider array as a pointer, so plus 1
  if (ty->isArrayTy())
    return 1 + getComplexity(ty->getArrayElementType());
  
  return 0; // default plus one
}

float computeEdgeComplexity(Function* F){
  int ret = 0; 

  if (F->getReturnType()->isVoidTy() && F->getArgumentList().empty())
    return 0;

  //  errs() << F->getName() 
  //	 << " how many args: " << F->getArgumentList().size() << "\n";
  ret = getComplexity(F->getReturnType());
  typeCache[F->getReturnType()] = ret;


  errs() << "retval complexity: " << ret << "\n";
  for (auto& A : F->getArgumentList()){
    if(F->getName() == "initialize_options")
      errs() << "A.getType: " << A.getType() << "\n";
    int arg_complexity = getComplexity(A.getType());
    errs() << "arg : " << *A.getType() << " " << arg_complexity << "\n";
    ret += arg_complexity; 
  }
  return ret;
}


void findEdgesWithLeak (vector<CallEdge>& CG, 
			vector<pair<string, string> >& edgesWithParamLeak, 
			vector<pair<string, string> >& edgesWithReturnLeak){

  set<string> callerP;
  set<string> calleeP;
  set<string> callerR;
  set<string> calleeR;

  for(auto &E : edgesWithParamLeak){
    callerP.insert(E.first);
    calleeP.insert(E.second);
  }
  for(auto &E : edgesWithReturnLeak){
    callerR.insert(E.first);
    calleeR.insert(E.second);
  }

  for (auto &E : CG){
    if(callerP.find(E.caller) != callerP.end() && calleeP.find(E.callee) != calleeP.end()){
      errs() << "Edge with parameter leak: " << E.caller << " ---> " << E.callee << "\n";
      E.param_leak = SECRET_FILE_SIZE*8;
    }
    if(callerR.find(E.caller) != callerR.end() && calleeR.find(E.callee) != calleeR.end()){
      errs() << "Edge with return leak: " << E.caller << " ---> " << E.callee << "\n";
      E.return_leak = 1;
    }
  }
}


void printFidSizeSetToFile(set<FidSize*>& S, set<FidSize*>& GS, string filename){
  ofstream outfile;
  outfile.open(filename);
  for(auto const &fs : S){
    outfile << fs->fname << " " << fs->fid << " " << fs->icount << "\n";
  }
  for(auto const &gs : GS){
    outfile << gs->fname << " " << gs->fid << " " << gs->icount << "\n";
  }
  
  outfile.close();
}


void printCallGraphToFile(vector<CallEdge>& CG, string filename){
  ofstream outfile;
  outfile.open(filename);
  for(auto const &E : CG){

    // global -> func
    if(E.caller[0] == '$'){
      outfile <<globalDict[E.caller] << " " << funcDict[E.callee] << " " 
	      << E.call_times << " " << E.type_complexity << " "
	      << E.param_leak << "/" << E.return_leak << "\n";
    }
    // func -> global
    else if (E.callee[0] == '$'){
      outfile <<funcDict[E.caller] << " " << globalDict[E.callee] << " " 
	      << E.call_times << " " << E.type_complexity << " "
	      << E.param_leak << "/" << E.return_leak << "\n";
    }
    // func -> func
    else{
      outfile <<funcDict[E.caller] << " " << funcDict[E.callee] << " " 
	      << E.call_times << " " << E.type_complexity << " "
	      << E.param_leak << "/" << E.return_leak << "\n";
    }
  }
  outfile.close();
}

void readCallSiteFromFile(set<CallSiteWrapper*>& S, string filename){
  ifstream infile(filename);
  string line;

  unsigned int tid, tline, tcalltimes;
  string tfunc, tfile, tdir;
 
  if (!infile.is_open()){
    errs() << "Fail to read CallSite, file can't be opened!\n ";
    exit(0);
  }

  while(infile >> tid >> tfunc >> tdir >> tfile >> tline >> tcalltimes){
    CallSiteWrapper* csw = new CallSiteWrapper(tid, nullptr, tfunc, tfile, 
					       tdir, tline, tcalltimes); 
    S.insert(csw);
  }
}

void readCallTimesFromPin(vector<CallPair>& vec, string filename){
  ifstream infile(filename);
  string line, caller, callee;
  
  if (!infile.is_open()){
    errs() << "Fail to read CallPair, file can't be opened!\n ";
    exit(0);
  }
  while (infile >> caller >> callee){
    CallPair cp(caller, callee);
    vec.push_back(cp);
  }
}


struct GetCallGraph : public ModulePass {
  static char ID;
  GetCallGraph() : ModulePass(ID) {}

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    ModulePass::getAnalysisUsage(AU);
    AU.addRequired<ProgramDependencyGraph>();
    AU.setPreservesAll();
  }

  bool runOnModule(Module &M) {

    ProgramDependencyGraph *PDG = &getAnalysis<ProgramDependencyGraph>();
    errs() << "PDG->getPassName: " << PDG->getPassName() << "\n";
    errs() << "PDG->senFuncs.size = " << PDG->senFuncs.size() << "\n";
    errs() << "PDG->insFuncs.size = " << PDG->insFuncs.size() << "\n";
    errs() << "edgesWithParamLeak.size = " << PDG->edgesWithParamLeak.size() << "\n";
    errs() << "edgesWithReturnLeak.size = " << PDG->edgesWithReturnLeak.size() << "\n";
    errs() << "==============BEGIN GetCallGraph Pass runOnModule: ==============" << "\n";

    // process all types in this module, find all recursive types(struct)
    TypeFinder StructTypes;
    StructTypes.run(M, true);
    for (auto *STy : StructTypes){
      set<Type*> prevTypes;
      prevTypes.insert(STy);
      //     errs() << "\n+++++++++++++++++++++++++++++++++++++++\n" << prevTypes.size()<<"\n";
      for(int i = 0; i < STy->getNumContainedTypes(); i++){
	Type* ty = STy->getContainedType(i);
	//	errs() << "ty [" << i <<" ]: " << *ty << "\n";	
	if (ty->isPointerTy()){
	  Type* baseTy = getNonPointerBaseTy(ty);

	  //	  Type* pteTy = ty->getContainedType(0);
	  if (recursiveTypes.find(baseTy) != recursiveTypes.end() || 
	      prevTypes.find(baseTy) != prevTypes.end()){
	    errs() << "recursive ty: " << *baseTy << "\n";
	    recursiveTypes.insert(baseTy);
	    prevTypes.insert(baseTy);
	  }
	  // TODO: adhoc processing for reciprocally called structs, see sshkey and sshkey_cert
	  if (baseTy->isStructTy()){
	    for (int i = 0; i < baseTy->getStructNumElements(); i++){
	      Type* tyi = getNonPointerBaseTy(baseTy->getStructElementType(i)); 
	      if (recursiveTypes.find(tyi) != recursiveTypes.end() ||
		  prevTypes.find(tyi) != prevTypes.end()){
		errs() << "deep recursive struct: " << *tyi << "\n";
		prevTypes.insert(tyi);
		recursiveTypes.insert(tyi);
	      }
	    }
	  }//end if baseTy->isStructTy
	}

	if (ty->isStructTy()){
	  
	  if (recursiveTypes.find(ty) != recursiveTypes.end() || 
	      prevTypes.find(ty) != prevTypes.end()){
	    errs() << "recursive ty: " << *ty << "\n";
	    recursiveTypes.insert(ty);
	    prevTypes.insert(ty);
	  }

	    for (int i = 0; i < ty->getStructNumElements(); i++){
	      Type* tyi = getNonPointerBaseTy(ty->getStructElementType(i)); 
	      if (recursiveTypes.find(tyi) != recursiveTypes.end() ||
		  prevTypes.find(tyi) != prevTypes.end()){
		errs() << "deep recursive struct: " << *tyi << "\n";
		prevTypes.insert(tyi);
		recursiveTypes.insert(tyi);
	      }
	    }
	}// end ty->isStructTy()
      }
      //      errs() << "\n---------------------------------------\n";
      prevTypes.clear();
      //  StructTyMap[STy] = complexity;
      // errs() << "complexity : " << complexity << "\n";
    }
    errs() << "recursive types:\n";
    errs() << "=======================================\n";
    for (auto const & I : recursiveTypes){
      errs() << *I << "\n";
    }


      
    errs() << "============== Start to construct StructTyMap ===============\n";

    // construct StructTyMap
    for (auto *STy : StructTypes){
      int complexity = 0;
      errs() << "Type: " << *STy << "\n";
      complexity = evaluateStructTy(STy);
      StructTyMap[STy] = complexity;
      errs() << "complexity : " << complexity << "\n";
    }    

    errs() << "=========== Start to generate profiling data...=============\n";

#if 1
    int fid = 0;
    ofstream func_id_file;
          func_id_file.open("./thttpd/thttpd_func_id_map.txt");
    //    func_id_file.open("./ssh/ssh_func_id_map.txt");
    //    func_id_file.open("./wget/wget_func_id_map.txt");
    //    func_id_file.open("./telnet/telnet_func_id_map.txt");


    set<CallPair> testS;
    for (Function &F : M){
      if (F.isDeclaration() || F.isIntrinsic())
	continue;

      funcDict[F.getName()] = fid;
      func_id_file << F.getName().str() << " " << funcDict[F.getName()] << "\n";

      //count instructions in F
      int NumInsts = 0;
      for (BasicBlock &B : F){
	NumInsts += B.getInstList().size();
      }

      funcSet.insert(F.getName());
      errs() << "Function: " << F.getName() << "fid: " << fid << " InstructionCount: " << NumInsts << "\n";
      FidSize *pfs = new FidSize(F.getName(), fid, NumInsts);
      fidSizeSet.insert(pfs);
      fid++;
      errs() << "fid: " << fid << "\n"; 

      for(BasicBlock &B : F){
	for(Instruction &I : B){
	  if (auto *CI = dyn_cast<CallInst>(&I)){
	    Function* callee = CI->getCalledFunction();
	    //e.g. %call = call i32 (i32, ...)* bitcast (i32 (i32)* @f to i32 (i32, ...)*)(i32 5), !dbg !30
	    if (callee == nullptr) continue;
	    if(CI->getCalledFunction()->isIntrinsic() || CI->getCalledFunction()->isDeclaration())
	      continue;
	    if (callee->isDeclaration() || callee->isIntrinsic())
	      continue;
		
	    // for call edges between two functions
	    CallEdge ce(F.getName(), CI->getCalledFunction()->getName(), 0, 0.0);
	    bool inCG = false;
	    for (const auto& E : CG){
	      if (E.caller == ce.caller && E.callee == ce.callee){
		inCG = true;
		break;
	      }
	    }
	    if (!inCG){
	      ce.type_complexity = computeEdgeComplexity(CI->getCalledFunction()) + 1;
	      errs() << "\n CALL EDGE <" <<F.getName() << " --> " << CI->getCalledFunction()->getName() << " > complexity: " << ce.type_complexity << "\n"; 
	      errs() << "FunctionTy: " << *CI->getCalledFunction()->getFunctionType() << "\n";
	      CG.push_back(ce);
	    } 
	  }
	}
      }// end for (BasicBlock...)
    }//end for F : M...

    // process call edges between global variables and functions 
    int gid = fid+1;
    
    errs() << "Now we are processing call edges between global variables and functions:\n";
    errs() << "globalTaintedFuncMap.size: " << PDG->globalTaintedFuncMap.size() << "\n";
    errs() << "gid: " << gid << "\n";

    for (auto & GF : PDG->globalTaintedFuncMap){
      string Str;
      raw_string_ostream OS(Str);

      OS << *(GF.first);
      string gv = OS.str();
      unsigned first = gv.find("@");
      unsigned last = gv.find("=") - 1;
      string strnew = gv.substr(first, last-first);
      strnew[0] = '$';

      // For @auth_check2.prevcryp, we only get auth_check2 for checking...
      first = strnew.find("$"); 
      last = strnew.find(".") - 1;
      // we can find an LLVM global like @auth_check2.prevcryp
      if (last != string::npos){
	string mayFunc = strnew.substr(first+1, last-first);
	// we skip this LLVM IR global because this is a static local variable
	if (funcSet.find(mayFunc) != funcSet.end()){
	  errs() << "Possible Function Name: " << mayFunc << "\n";
	  continue;
	}
      }
      

     FidSize *pfs = new FidSize(strnew, gid, -1);
     fidSizeSetForGlobals.insert(pfs);

     globalDict[strnew] = gid;
     gid++;
     errs() << strnew << " gid: " << gid << "\n"; 

      for (auto &F : GF.second){
	// CallEdge: src dest call_times type_complexity
	int type_complexity = getComplexity(GF.first->getType());
	errs() << "Global: " << strnew << "\n"; 
	errs() << "Global type complexity: " << type_complexity << "\n";
	CallEdge gce(strnew, F->getName().str(), 0, type_complexity);
	CallEdge cge(F->getName().str(), strnew, 0, type_complexity);

	bool gceInCG = false;
	for (const auto& E : CG){
	  if (E.caller == gce.caller && E.callee == gce.callee){
	    gceInCG = true;
	    break;
	  }
	}
	if (!gceInCG){
	  errs() << "\n gce CALL EDGE <" <<gce.caller << " --> " << gce.callee<< "  complexity: " << gce.type_complexity << "\n"; 
	  errs() << "globale type: " << *GF.first->getType() << "\n";
	  CG.push_back(gce);
	} 

	bool cgeInCG = false;
	for (const auto& E : CG){
	  if (E.caller == cge.caller && E.callee == cge.callee){
	    cgeInCG = true;
	    break;
	  }
	}
	if (!cgeInCG){
	  errs() << "\n cge CALL EDGE <" <<cge.caller << " --> " << cge.callee<< "  complexity: " << cge.type_complexity << "\n"; 
	  errs() << "globale type: " << *GF.first->getType() << "\n";
	  CG.push_back(cge);
	} 
      }
    }// end auto & GF : PDG->globalTaintedFuncMap
      
    func_id_file.close();

    errs() << "call graph size: " << CG.size() << "\n";
    errs() << "non redundant call edges: " << testS.size() << "\n";

        readCallTimesFromPin(callPairsFromPin, "./thttpd/thttpd.pinout.txt");
    //    readCallTimesFromPin(callPairsFromPin, "./ssh/ssh.calltimes");
    //    readCallTimesFromPin(callPairsFromPin, "./wget/wget.pin.output");
    //    readCallTimesFromPin(callPairsFromPin, "./telnet/telnet.pin.output");

    set<string> invokedF;
    for (const auto& P : callPairsFromPin){
      for (auto& E : CG){
	if(invokedF.find(E.caller) == invokedF.end())
	  invokedF.insert(E.caller);
	if(invokedF.find(E.callee) == invokedF.end())
	  invokedF.insert(E.callee);

	if (P.caller == E.caller && P.callee == E.callee){
	  E.call_times++;
	  errs() << "Found runtime call " << E.caller << " " << E.callee << "\n";
	}
      }
    }

            string sourceFunc = "auth_check2";
    //	string sourceFunc = "sshkey_parse_private2";
    //    string sourceFunc = "fd_read_body";
    //string sourceFunc = "process_rings";

    errs() << "invoked funcs: " << invokedF.size() << "\b";
    errs() << "sensitive func: " << funcDict[sourceFunc] << "\n";
    errs() << "main func: " << funcDict["main"] << "\n";


    findEdgesWithLeak(CG, PDG->edgesWithParamLeak, PDG->edgesWithReturnLeak);

           printCallGraphToFile(CG, "./thttpd/thttpd.callgraph");
    //    printCallGraphToFile(CG, "./ssh/ssh.callgraph");
    //       printCallGraphToFile(CG, "./wget/wget.callgraph");
    //       printCallGraphToFile(CG, "./telnet/telnet.callgraph");

    errs() << "CallPairsFromPin: " << callPairsFromPin.size() << "\n";

    int temp = 0;
    for(const auto& CP : callPairsFromPin){
      if ((funcSet.find(CP.caller) != funcSet.end()) &&
	  (funcSet.find(CP.callee) != funcSet.end()) ){
	temp++;
      }
    }
    errs() << "real callpairs: " << temp << "\n";


    printFidSizeSetToFile(fidSizeSet, fidSizeSetForGlobals, "./thttpd_id_code_size.txt");
    //       printFidSizeSetToFile(fidSizeSet, fidSizeSetForGlobals, "./ssh_id_code_size.txt");
    //       printFidSizeSetToFile(fidSizeSet, fidSizeSetForGlobals, "./wget/wget_id_code_size.txt");
    //   printFidSizeSetToFile(fidSizeSet, fidSizeSetForGlobals, "./telnet/telnet_id_code_size.txt");


    fidSizeSet.clear();
    callPairsFromPin.clear();
    errs() << "===============END GetCallGraph Pass runOnModule: ===============" << "\n";

#endif
    return false;
  }
};


char GetCallGraph::ID = 0;
static RegisterPass<GetCallGraph> GCG("get-call-graph", "Get Call Graph Pass",
				      false /* Only looks at CFG */,
				      false /* Analysis Pass */);




