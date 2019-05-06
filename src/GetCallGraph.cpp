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
#include "llvm/IR/Value.h"
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

#define THTTPD_EXTRA_OPERATION 0 
#define TELNET_EXTRA_OPERATION 0 
#define WGET_EXTRA_OPERATION 0
#define SSH_EXTRA_OPERATION 0

#define REAL_TIME 0.013


using namespace std;
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

set<string> ssh_client_global_set;
set<string> ssh_client_only_set;

vector<CallPair> callPairsFromPin;

vector<CallEdge> CG; // static call graph

set<string> funcNameSet;
set<string> globalNameSet;
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
    //   errs() << "STy is in typeCache, typeCache.size: " << typeCache.size() << "\n";
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
	  errs() << "pteTy = " << *pteTy << "\n";
	  errs() << "elem++\n";
	  elem++;
	  pteTy = pteTy->getContainedType(0);
	}
	errs() << "after while elem = : " << elem << "\n";
      }
      // why i8* always 0? check ty first...
      else elem++; // default, e.g.: ty:i8* pteTy: i8, elem++ = 1...
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
    // errs() << "Cache ty = " << *STy << " complexity: " << max << "\n";
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
      //   errs() << "FunctionTy found\n";
      // errs() << *ty->getContainedType(0) << "\n";
      return 1;
    }
    return 1 + getComplexity(ty->getContainedType(0));
  }

  // TODO: is 1 OK for FunctionTy?
  if (ty->isFunctionTy()){
    // errs() << "ty is FunctionTy: " << *ty << "\n";
    return 1;
  }
  // we consider array as a pointer, so plus 1
  if (ty->isArrayTy())
    return 1 + getComplexity(ty->getArrayElementType());
  
  return 0; // default plus one
}


int getGlobalTypeComplexity(Type* ty){
  if (ty == nullptr) return 0;

  if(ty->isStructTy()){
    errs() << "g StructTy: " << *ty << "\n";
    errs() << "StructTyMap[ty]: " << StructTyMap[ty] << "\n"; 
    return StructTyMap[ty];
  }
  // take care of recursive types. e.g. linked list
  if (ty->isPointerTy()){
    // if i8* (char*)
    //    if (isInt8PointerTy(ty->getContainedType(0)))
    //  return 1;
    errs() << "g isPointerTy: " << *ty << "\n";
    if (ty->getContainedType(0)->isFunctionTy()){
      //   errs() << "FunctionTy found\n";
      // errs() << *ty->getContainedType(0) << "\n";
      return 1;
    }
    return 1 + getGlobalTypeComplexity(ty->getContainedType(0));
  }

  // TODO: is 1 OK for FunctionTy?
  if (ty->isFunctionTy()){
    // errs() << "ty is FunctionTy: " << *ty << "\n";
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

  ret = getComplexity(F->getReturnType());
  typeCache[F->getReturnType()] = ret;

  //  errs() << "retval complexity: " << ret << "\n";
  for (auto& A : F->getArgumentList()){
    if(F->getName() == "initialize_options")
      errs() << "A.getType: " << A.getType() << "\n";
    int arg_complexity = getComplexity(A.getType());
    //  errs() << "arg : " << *A.getType() << " " << arg_complexity << "\n";
    ret = (ret > arg_complexity) ? ret : arg_complexity; 
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
      E.param_leak = SSH_EXTRA_OPERATION ? SECRET_FILE_SIZE*8 : 1;
    }
    if(callerR.find(E.caller) != callerR.end() && calleeR.find(E.callee) != calleeR.end()){
      errs() << "Edge with return leak: " << E.caller << " ---> " << E.callee << "\n";
      E.return_leak = 1;
    }
  }
}

void findEdgesWithPotentialLeak (vector<CallEdge>& CG, 
			vector<pair<string, string> >& edgesWithPotentialLeakFromArgs, 
			vector<pair<string, string> >& edgesWithPotentialLeakFromRet){
  set<string> callerP;
  set<string> calleeP;
  set<string> callerR;
  set<string> calleeR;

  for(auto &E : edgesWithPotentialLeakFromArgs){
    callerP.insert(E.first);
    calleeP.insert(E.second);
  }
  for(auto &E : edgesWithPotentialLeakFromRet){
    callerR.insert(E.first);
    calleeR.insert(E.second);
  }

  for (auto &E : CG){
    if(callerP.find(E.caller) != callerP.end() && calleeP.find(E.callee) != calleeP.end()){
      errs() << "Edge with Potential leak through args: " << E.caller << " ---> " << E.callee << "\n";
      E.param_leak = SECRET_FILE_SIZE*8;
    }
    if(callerR.find(E.caller) != callerR.end() && calleeR.find(E.callee) != calleeR.end()){
      errs() << "Edge with potential leak through ret: " << E.caller << " ---> " << E.callee << "\n";
      E.return_leak = SECRET_FILE_SIZE*8;
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


void printCallGraphToFile(vector<CallEdge>& CG, string filename,
			  int funcs, int dimension, int senFuncID, int mainID){
  ofstream outfile;
  outfile.open(filename);

  outfile << funcs << "\n" << dimension << "\n" << senFuncID << "\n" << mainID << "\n";

  for(auto const &E : CG){
    // global -> func
    if(E.caller[0] == '$'){
      outfile << globalDict[E.caller] << " " << funcDict[E.callee] << " " 
	      << E.call_times/REAL_TIME << " " << E.type_complexity << " "
	      << E.param_leak << "/" << E.return_leak << "\n";
    }
    // func -> global
    else if (E.callee[0] == '$'){
      outfile << funcDict[E.caller] << " " << globalDict[E.callee] << " " 
	      << E.call_times/REAL_TIME << " " << E.type_complexity << " "
	      << E.param_leak << "/" << E.return_leak << "\n";
    }
    // func -> func
    else{
      outfile << funcDict[E.caller] << " " << funcDict[E.callee] << " " 
	      << E.call_times/REAL_TIME << " " << E.type_complexity << " "
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


void readSSHClientFuncsFromFile(set<string>& S, string filename){
  ifstream infile(filename);
  string funcstr;
  
  if (!infile.is_open()){
    errs() << "Fail to read SSHClientFuncs, file can't be opened!\n ";
    exit(0);
  }
  while (infile >> funcstr){
    S.insert(funcstr);
  }
}

void readSSHClientGlobalsFromFile(set<string>& S, string filename){
  ifstream infile(filename);
  string globalstr;
  
  if (!infile.is_open()){
    errs() << "Fail to read SSHClientGlobals, file can't be opened!\n ";
    exit(0);
  }
  while (infile >> globalstr){
    S.insert(globalstr);
  }
}



void printSSHFuncLabelsToFile(set<FidSize*>& S,
			      set<FidSize*>& GS,
			      set<string>& ssh_client_only_set,
			      set<string>& ssh_client_global_set, 
			      string filename){
  ofstream outfile;
  outfile.open(filename);
  for(auto const &fs : S){
    if (ssh_client_only_set.find(fs->fname) != ssh_client_only_set.end())
      outfile << fs->fname << " " << fs->fid << " " << 1 << "\n";
    else
      outfile << fs->fname << " " << fs->fid << " " << 0 << "\n";
  }

  for(auto const &gs : GS){
    if (ssh_client_global_set.find(gs->fname) != ssh_client_global_set.end())
      outfile << gs->fname << " " << gs->fid << " " << 1 << "\n";
    else
      outfile << gs->fname << " " << gs->fid << " " << 0 << "\n";     
  }

  outfile.close();
  
}

bool isPinInCG(string caller, string callee, vector<CallEdge>& CG){
  bool ret = false;
  for (auto const& E : CG){
    if (caller == E.caller && callee == E.callee){
      ret = true;
      break;
    }
  }
  return ret;
}


void insertToCallGraph(Function* caller, Function* callee, vector<CallEdge>& CG){
  CallEdge ce(caller->getName(), callee->getName(), 0, 0.0);
  bool inCG = false;
  for (const auto& E : CG){
    if (E.caller == ce.caller && E.callee == ce.callee){
      inCG = true;
      //      E.call_times++;
      break;
    }
  }
  if (!inCG){
    ce.type_complexity = computeEdgeComplexity(callee) + 1;
    errs() << "\n Indirect CALL EDGE <" <<caller->getName() << " --> " << callee->getName() << " > complexity: " << ce.type_complexity << "\n"; 
    // errs() << "FunctionTy: " << *CI->getCalledFunction()->getFunctionType() << "\n";
    CG.push_back(ce);
  } 
}

typedef struct{
  string func_id_map_filename;
  string pin_filename;
  string source_funcname;
  string callgraph_filename;
  string id_code_size_filename;
}ProgramConfig;

enum{
  THTTPD,
  SSH,
  WGET,
  TELNET,
  CHSH,
  CHAGE,
  PASSWD,
  USERADD
};


void input_output_filename_init(string program_name, ProgramConfig& pconfig){

  if (program_name.empty()){
    errs() << "Empty program name input!\n";
    exit(1);
  }
  // example: "./wget/wget_func_id_map.txt"
  pconfig.func_id_map_filename = "./" + program_name + "/" + program_name + "_func_id_map.txt";

  // example: "./wget/wget.pin.txt"  
  pconfig.pin_filename = "./" + program_name + "/" + program_name + ".pin.txt";

  int prog = -1;
  if (program_name == "thttpd")
    prog = THTTPD;
  if (program_name == "ssh")
    prog = SSH;
  if (program_name == "wget")
    prog = WGET;
  if (program_name == "telnet")
    prog = TELNET;

  if (program_name == "chsh")
    prog = CHSH;

  if (program_name == "chage")
    prog = CHAGE;

  if (program_name == "passwd")
    prog = PASSWD;

  if (program_name == "useradd")
    prog = USERADD;

  switch(prog)
    {
    case THTTPD:
      pconfig.source_funcname = "auth_check2";
      break;
    case SSH:
      pconfig.source_funcname = "sshkey_parse_private2";
      break;
    case WGET:
      pconfig.source_funcname = "sock_read";
      break;
    case TELNET:
      pconfig.source_funcname = "process_rings";
      break;
    case CHSH:
      pconfig.source_funcname = "update_shell";
      break;
    case CHAGE:
      pconfig.source_funcname = "chage_get_user_fields";
      break;

    case PASSWD:
      pconfig.source_funcname = "passwd_core";
      break;

    case USERADD:
      pconfig.source_funcname = "open_files";
      break;

    default:
      ;
    }  
  
  // example: "./wget/wget.callgraph"
  pconfig.callgraph_filename = "./" + program_name + "/" + program_name + ".callgraph";

  // example: ./wget/wget_id_code_size.txt
  pconfig.id_code_size_filename = "./" + program_name + "/" + program_name + "_id_code_size.txt";

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

    ProgramConfig pconfig;
 
    // now we are processing chage
    string program_name = "chage";

    input_output_filename_init(program_name, pconfig);

    errs() << "func_id_map_file   : " << pconfig.func_id_map_filename << "\n";
    errs() << "pin_filename       : " << pconfig.pin_filename << "\n";
    errs() << "source_funcname    : " << pconfig.source_funcname << "\n";
    errs() << "callgraph_file     : " << pconfig.callgraph_filename << "\n";
    errs() << "id_code_size_file  : " << pconfig.id_code_size_filename << "\n";

    ProgramDependencyGraph *PDG = &getAnalysis<ProgramDependencyGraph>();
    errs() << "PDG->getPassName: " << PDG->getPassName() << "\n";
    errs() << "PDG->senFuncs.size = " << PDG->senFuncs.size() << "\n";
    errs() << "PDG->insFuncs.size = " << PDG->insFuncs.size() << "\n";
    errs() << "edgesWithParamLeak.size = " << PDG->edgesWithParamLeak.size() << "\n";
    errs() << "edgesWithReturnLeak.size = " << PDG->edgesWithReturnLeak.size() << "\n";
    errs() << "edgesWithPotentialLeakFromArgs.size = " << PDG->edgesWithPotentialLeakFromArgs.size() << "\n";
    errs() << "edgesWithPotentialLeakFromRet.size = " << PDG->edgesWithPotentialLeakFromRet.size() << "\n";
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


#if SSH_EXTRA_OPERATION
    readSSHClientFuncsFromFile(ssh_client_only_set, "./ssh/ssh-only-client-functions.txt");
    errs() << "ssh_client_only_set.size: " << ssh_client_only_set.size() << "\n";

    readSSHClientGlobalsFromFile(ssh_client_global_set, "./ssh/global_in_ssh_client.txt");
    errs() << "global_in_ssh_client.size: " << ssh_client_global_set.size() << "\n";
#endif

#if 1
    int fid = 0;
    ofstream func_id_file;

    // func_id_file.open("./thttpd/thttpd_func_id_map.txt");
    // func_id_file.open("./ssh/ssh_func_id_map.txt");
    // func_id_file.open("./wget/wget_func_id_map.txt");
    // func_id_file.open("./telnet/telnet_func_id_map.txt");

    func_id_file.open(pconfig.func_id_map_filename);

    set<CallPair> testS;
    set<Function*> funcSet;
    for (Function &F : M){
      if (F.isDeclaration() || F.isIntrinsic())
	continue;

      funcSet.insert(&F);
    }
    errs() << "funcSet.size: " << funcSet.size() << "\n";

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

      funcNameSet.insert(F.getName());
      errs() << "Function: " << F.getName() << "fid: " << fid << " InstructionCount: " << NumInsts << "\n";
      FidSize *pfs = new FidSize(F.getName(), fid, NumInsts);
      fidSizeSet.insert(pfs);
      fid++;

      for(BasicBlock &B : F){
	for(Instruction &I : B){
   
	  if (auto *CI = dyn_cast<CallInst>(&I)){
	    Function* callee = CI->getCalledFunction();
	    //e.g. %call = call i32 (i32, ...)* bitcast (i32 (i32)* @f to i32 (i32, ...)*)(i32 5), !dbg !30
	    if (callee == nullptr) {
	      errs() << "CALLEE==NULLPTR: " << *CI << "\n";
// disable handling indirect call with bitcasts 
#if 0
	      Type* ty = CI->getCalledValue()->getType();
	      FunctionType* fty = cast<FunctionType>(cast<PointerType>(ty)->getElementType());

	      // %call111 = call i32 bitcast (i32 (%struct.ssh*, i8)* @sshpkt_start to 
	      // i32 (%struct.ssh.68*, i8)*)(%struct.ssh.68* %100, i8 zeroext 80), !dbg !14101
	      // get the function from the CallInst with BitCast
	      Function* calleeInBitCast = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts());
	      if (calleeInBitCast != nullptr){
		errs() << "calleeInBitCast: " << calleeInBitCast->getName() << "\n";
		insertToCallGraph(&F, calleeInBitCast, CG);
	      }

	      for(auto &FP : funcSet){
		if (FP->getFunctionType() == fty){
		  errs() << "fty: " << *fty << "\n";
		  errs() << "candidate jump to function: " << FP->getName() << "\n";

		  insertToCallGraph(&F, FP, CG);
		}
	      }
#endif
	      continue;
	    }
	    if (callee->isDeclaration() || callee->isIntrinsic()) continue;

	    //  %25 = load %struct.cauthmethod** %method12, align 8, !dbg !26174
	    //  %userauth = getelementptr inbounds %struct.cauthmethod* %25, i32 0, i32 1, !dbg !26174
	    //  %26 = load i32 (%struct.cauthctxt*)** %userauth, align 8, !dbg !26174
	    //  %27 = load %struct.cauthctxt** %authctxt.addr, align 8, !dbg !26174
	    //  %call17 = call i32 %26(%struct.cauthctxt* %27), !dbg !26174
	    //  indirect call, called Type t = i32 (%struct.cauthctxt*)* 

	    // for call edges between two functions
	    insertToCallGraph(&F, CI->getCalledFunction(), CG);
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
	if (funcNameSet.find(mayFunc) != funcNameSet.end()){
	  errs() << "Possible Function Name: " << mayFunc << "\n";
	  continue;
	}
      }
      
      FidSize *pfs = new FidSize(strnew, gid, -1);
      fidSizeSetForGlobals.insert(pfs);
      globalDict[strnew] = gid;
      globalNameSet.insert(strnew);
      gid++;

    // static call relationship between functions and global variables
#if 0    
      for (auto &F : GF.second){
	// CallEdge: src dest call_times type_complexity
	int type_complexity = getGlobalTypeComplexity(GF.first->getType());
	CallEdge gce(strnew, F->getName().str(), 0, type_complexity);
	CallEdge cge(F->getName().str(), strnew, 0, type_complexity);

	bool gceInCG = false;
	for (const auto& E : CG){
	  if (E.caller == gce.caller && E.callee == gce.callee){
	    gceInCG = true;
	    break;
	  }
	}
	if (!gceInCG)
	  CG.push_back(gce);

	bool cgeInCG = false;
	for (const auto& E : CG){
	  if (E.caller == cge.caller && E.callee == cge.callee){
	    cgeInCG = true;
	    break;
	  }
	}
	if (!cgeInCG){
	  cge.type_complexity = getGlobalTypeComplexity(GF.first->getType());
	  errs() << "\n cge CALL EDGE <" <<cge.caller << " --> " << cge.callee<< "  new complexity: " << cge.type_complexity << "\n"; 
	  errs() << "globale type: " << *GF.first->getType() << "\n";
	  CG.push_back(cge);
	} 
      }
#endif     
    }// end auto & GF : PDG->globalTaintedFuncMap
 
    func_id_file.close();

    errs() << "call graph size: " << CG.size() << "\n";
    errs() << "non redundant call edges: " << testS.size() << "\n";

    // readCallTimesFromPin(callPairsFromPin, "./thttpd/thttpd.pin.txt");
    // readCallTimesFromPin(callPairsFromPin, "./ssh/ssh.pin.txt");
    // readCallTimesFromPin(callPairsFromPin, "./wget/wget.pin.txt");
    // readCallTimesFromPin(callPairsFromPin, "./telnet/telnet.pin.txt");

    readCallTimesFromPin(callPairsFromPin, pconfig.pin_filename);

    errs() << "globalNameSet.size: " << globalNameSet.size() << "\n";
    errs() << "funcNameSet.size: " << funcNameSet.size() << "\n";

    set<string> global_func_set;
    global_func_set.insert(globalNameSet.begin(), globalNameSet.end());
    global_func_set.insert(funcNameSet.begin(), funcNameSet.end());

    /*
    ofstream tempout;
    tempout.open("./global_func_set.txt");
    for(auto const &gf : global_func_set){
      tempout << gf << "\n";
    }
    tempout.close();
    */
       
    int temp = 0;

    for(const auto& CP : callPairsFromPin){
      if ((global_func_set.find(CP.caller) != global_func_set.end()) &&
	  (global_func_set.find(CP.callee) != global_func_set.end()) ){
	temp++;

	if (!isPinInCG(CP.caller, CP.callee, CG)){
	  //	  errs() << "pin_callgraph_WARNING: " << CP.caller << " " << CP.callee << "\n";
	  // add missing call edge between two functions (caused by indirect calls)
	  if (CP.caller[0] != '$' && CP.callee[0] != '$'){
	    Function* caller;
	    Function* callee;
	    for (auto& FP : funcSet){
	      if (FP->getName() == CP.caller)
		caller = FP;
	      
	      if (FP->getName() == CP.callee)
		callee = FP;
	    }
	    insertToCallGraph(caller, callee, CG);
	    errs() << "Warning_fixed: " << CP.caller << " " << CP.callee << "\n";
	  }

	  // add missing call edge from function to global
	  if (CP.caller[0] != '$' && CP.callee[0] == '$'){
	    for (auto & GF : PDG->globalTaintedFuncMap){
	      string Str;
	      raw_string_ostream OS(Str);

	      OS << *(GF.first);
	      string gv = OS.str();
	      unsigned first = gv.find("@");
	      unsigned last = gv.find("=") - 1;
	      string strnew = gv.substr(first, last-first);
	      strnew[0] = '$';
      
	      if (CP.callee == strnew){
		int type_complexity = getComplexity(GF.first->getType());
		CallEdge cge(CP.caller, strnew, 0, type_complexity);
		bool cgeInCG = false;

		for (const auto& E : CG){
		  if (E.caller == cge.caller && E.callee == cge.callee){
		    cgeInCG = true;
		    break;
		  }
		}
		if (!cgeInCG)
		  CG.push_back(cge);
		//		errs() << "cge_Warning_fixed: " << CP.caller << " " << CP.callee << "\n";
		break;
	      }
	    }// end auto & GF : PDG->globalTaintedFuncMap
	  }

	  // add missing call edge from global to function
	  if (CP.caller[0] == '$' && CP.callee[0] != '$'){
	    for (auto & GF : PDG->globalTaintedFuncMap){
	      string Str;
	      raw_string_ostream OS(Str);

	      OS << *(GF.first);
	      string gv = OS.str();
	      unsigned first = gv.find("@");
	      unsigned last = gv.find("=") - 1;
	      string strnew = gv.substr(first, last-first);
	      strnew[0] = '$';

	      if (strnew == CP.caller){
		int type_complexity = getComplexity(GF.first->getType());		
		CallEdge gce(strnew, CP.callee, 0, type_complexity);

		bool gceInCG = false;
		for (const auto& E : CG){
		  if (E.caller == gce.caller && E.callee == gce.callee){
		    gceInCG = true;
		    break;
		  }
		}
		if (!gceInCG)
		  CG.push_back(gce);
		errs() << "gce_Warning_fixed: " << CP.caller << " " << CP.callee << "\n";
		break;
	      }
	    }// end auto & GF : PDG->globalTaintedFuncMap
	  }
	}// 	if (!isPinInCG(CP.caller, CP.callee, CG))
      }	
    }
    errs() << "real callpairs: " << temp << "\n";
    errs() << "global_func_set.txt closed\n";
    errs() << "callPairsFromPin.size: " << callPairsFromPin.size() << "\n";
    errs() << "CG.size: " << CG.size() << "\n";
    set<string> invokedF;
    int count = 0;
    int range = 0;

    // add call times on edges
    for (const auto& P : callPairsFromPin){
      count++;
      if(count > 1000){
	count = 0;
	range += 1000;
	errs() << "ratio: " << 1.0*range/callPairsFromPin.size() << "\n";
      }

      for (auto& E : CG){
	if(invokedF.find(E.caller) == invokedF.end())
	  invokedF.insert(E.caller);
	if(invokedF.find(E.callee) == invokedF.end())
	  invokedF.insert(E.callee);

	if (P.caller == E.caller && P.callee == E.callee)
	  E.call_times++;
      }
    }

    // string sourceFunc = "auth_check2";
    // string sourceFunc = "sshkey_parse_private2";
    // string sourceFunc = "sock_read";
    // string sourceFunc = "process_rings";

    errs() << "invoked funcs: " << invokedF.size() << "\b";
    errs() << "sensitive func: " << funcDict[pconfig.source_funcname] << "\n";
    errs() << "main func: " << funcDict["main"] << "\n";

    findEdgesWithLeak(CG, PDG->edgesWithParamLeak, PDG->edgesWithReturnLeak);

    // findEdgesWithPotentialLeak (CG, PDG->edgesWithPotentialLeakFromArgs, PDG->edgesWithPotentialLeakFromRet);

    // printCallGraphToFile(CG, "./thttpd/thttpd.callgraph", invokedF.size(), 4, funcDict[sourceFunc], funcDict["main"]);
    // printCallGraphToFile(CG, "./ssh/ssh.callgraph", invokedF.size(), 4, funcDict[sourceFunc], funcDict["main"]);
    // printCallGraphToFile(CG, "./wget/wget.callgraph", invokedF.size(), 4, funcDict[sourceFunc], funcDict["main"]);
    // printCallGraphToFile(CG, "./telnet/telnet.callgraph", invokedF.size(), 4, funcDict[sourceFunc], funcDict["main"]);

    printCallGraphToFile(CG, pconfig.callgraph_filename, invokedF.size(), 4, funcDict[pconfig.source_funcname], funcDict["main"]);

    errs() << "CallPairsFromPin: " << callPairsFromPin.size() << "\n";

    // printFidSizeSetToFile(fidSizeSet, fidSizeSetForGlobals, "./thttpd_id_code_size.txt");
    // printFidSizeSetToFile(fidSizeSet, fidSizeSetForGlobals, "./ssh/ssh_id_code_size.txt");
    // printFidSizeSetToFile(fidSizeSet, fidSizeSetForGlobals, "./wget/wget_id_code_size.txt");
    // printFidSizeSetToFile(fidSizeSet, fidSizeSetForGlobals, "./telnet/telnet_id_code_size.txt");

    printFidSizeSetToFile(fidSizeSet, fidSizeSetForGlobals, pconfig.id_code_size_filename);

    // TODO: only for ssh, use SSH macro later
#if SSH_EXTRA_OPERATION
        printSSHFuncLabelsToFile(fidSizeSet, fidSizeSetForGlobals, ssh_client_only_set, ssh_client_global_set, "./ssh/ssh_in_libssa_or_not.txt");
#endif

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




