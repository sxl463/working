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
  int implicit_leak;
  int explicit_leak;

  CallEdge(string _caller, string _callee, int _call_times, float _type_complexity){
    caller = _caller;
    callee = _callee;
    call_times = _call_times;
    type_complexity = _type_complexity;
    implicit_leak = 0;
    explicit_leak = 0; 
  }
};


extern std::set<FunctionWrapper*> sen_FuncSet;
extern std::set<FunctionWrapper*> ins_FuncSet;


static unsigned int call_site_id = 0;

set<CallSiteWrapper*> cswSet;
set<CallSiteWrapper*> cswSetFromFile;

vector<CallPair> callPairsFromPin;

vector<CallEdge> CG; // static call graph


map<string, vector<int> > gcovDict;

set<string> funcSet;
map<string, int> funcDict;
set<FidSize*> fidSizeSet;

using namespace std;
using namespace cot;
using namespace llvm;


static set<string> existedFiles;

int NumFields = 0;
set<Type*> existedTypes;


bool isInt8PointerTy(Type* ty){
  if(PointerType *PT = dyn_cast<PointerType>(ty))
    if (IntegerType *IT = dyn_cast<IntegerType>(PT->getPointerElementType()))
      if (IT->getBitWidth() == 8)
	return true;

  return false;
}

int getComplexity(Type* ty){

  NumFields++;

  if(ty->isPointerTy() || ty->isStructTy()){
    //if this type is already existed, which means we have a recursive type
    if(existedTypes.find(ty) != existedTypes.end() &&
       !isInt8PointerTy(ty)){
      //     errs() << "existedTypes: " << existedTypes.size() << "\n";
      //  errs() << "existed type found: " << **existedTypes.find(ty) << "\n";
      existedTypes.clear();
      // errs() << "after clear, existedTypes: " << existedTypes.size() << "\n";
      return 100;
    }
    existedTypes.insert(ty);
  }

  // take care of recursive types. e.g. linked list
  if (ty->isPointerTy()){
    string Str;
    raw_string_ostream OS(Str);
    OS << *ty;
    //FILE*, bypass, no need to continue
    if("%struct._IO_FILE*" == OS.str() || 
       "%struct._IO_marker*" == OS.str())
      return 1000;
    //check if this is a recursive type
    if (ty->getContainedType(0)->isStructTy()){
      Type* sTy = ty->getContainedType(0);
      for(int i = 0; i < sTy->getStructNumElements(); i++)
	if (sTy->getStructElementType(i) == ty)
	  return 100;
    }
    return 1 + getComplexity(ty->getContainedType(0));
  }
  if (ty->isFunctionTy())
    return 100;
  
  if (ty->isArrayTy())
    return getComplexity(ty->getArrayElementType());
  

  if (ty->isStructTy()){		
    int sum = 0;
    for (int i = 0; i < ty->getStructNumElements(); i++)
      sum += getComplexity(ty->getStructElementType(i));
    
    return sum;
  }
  else
    return 0;
}

float computeEdgeComplexity(Function* F){
  float ret;

  NumFields = 0;

  //  errs() << "F->ReturnType: " << *F->getReturnType() <<"\n";
  // errs() << "call func: " << F->getName() << "args: " << F->getArgumentList().size() << "\n";
  ret = getComplexity(F->getReturnType());
  for (auto& A : F->getArgumentList()){
    ret += getComplexity(A.getType()); 
  }
  //  errs() << "arglist size: " << FunctionWrapper::funcMap[F]->getArgWList().size() << "\n";
  errs() << "NumFields: " << NumFields << "\n";
  return ret + 1.0/NumFields;
}



void printFidSizeSetToFile(set<FidSize*>& S, string filename){
  ofstream outfile;
  outfile.open(filename);
  for(auto const &fs : S){
    outfile << fs->fname << " " << fs->fid << " " << fs->icount << "\n";
  }
  outfile.close();
}


void printCallGraphToFile(vector<CallEdge>& CG, string filename){
  ofstream outfile;
  outfile.open(filename);
  for(auto const &E : CG){
    outfile << E.caller << " " << E.callee << " " 
	    << E.call_times << " " << E.type_complexity << " "
            << E.implicit_leak << " " << E.explicit_leak << "\n";
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


void findEdgesWithImplicitLeak(vector<CallEdge>& CG, string source){

  errs() << "sourceFunc: " << source << "\n";

  queue<string> worklist;
  worklist.push(source);
  set<string> visitedF;

  while(!worklist.empty()){
    string curr = worklist.front();
    worklist.pop();
    errs() << "curr: " << curr << "\n";
    for(auto &E : CG){
      if(E.callee == curr && 
	 visitedF.find(E.caller) == visitedF.end()){
	//	errs() << "implicit leak source function found!\n";
	E.implicit_leak = 1;
	visitedF.insert(E.caller);
	worklist.push(E.caller);
      }
    }
    errs() << "worklist size: " << worklist.size() << "\n";
  }

}

void findEdgesWithForwardLeak(vector<CallEdge>& CG, const set<string>& S){
  for (auto &E : CG){
    if(S.find(E.caller) != S.end() && S.find(E.callee) != S.end()){
      errs() << "Edge with forward leak: " << E.caller << " ---> " << E.callee << "\n";
      E.explicit_leak = 1;
    }
  }
}

//namespace cot{
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
    errs() << "==============BEGIN GetCallGraph Pass runOnModule: ==============" << "\n";

    int fid = 0;

    set<CallPair> testS;
    for (Function &F : M){
      if (F.isDeclaration() || F.isIntrinsic())
	continue;

      funcDict[F.getName()] = fid;

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

      for(BasicBlock &B : F){
	for(Instruction &I : B){
	  if (auto *CI = dyn_cast<CallInst>(&I)){
	    Function* callee = CI->getCalledFunction();
	    //e.g. %call = call i32 (i32, ...)* bitcast (i32 (i32)* @f to i32 (i32, ...)*)(i32 5), !dbg !30
	    if (callee == nullptr)
	      continue;
	    if(CI->getCalledFunction()->isIntrinsic() || CI->getCalledFunction()->isDeclaration())
	      continue;
	    if (callee->isDeclaration() || callee->isIntrinsic())
	      continue;
		
	    //	    errs() << "getCalledFunction: " << CI->getCalledFunction()->getName() << "\n";
	    // CallPair cp(F.getName(), CI->getCalledFunction()->getName());
	    CallEdge ce(F.getName(), CI->getCalledFunction()->getName(), 0, 0.0);
	    bool inCG = false;
	    for (const auto& E : CG){
	      if (E.caller == ce.caller && E.callee == ce.callee){
		inCG = true;
		break;
	      }
	    }
	    if (!inCG){
	      ce.type_complexity = computeEdgeComplexity(CI->getCalledFunction());
	      errs() << "CALL EDGE <" <<F.getName() << " --> " << CI->getCalledFunction()->getName() << " > complexity: " << ce.type_complexity << "\n"; 
	      CG.push_back(ce);
	    } 
	  }
	}
      }
	
    }//end for Function
      
    errs() << "call graph size: " << CG.size() << "\n";
    errs() << "non redundant call edges: " << testS.size() << "\n";

    readCallTimesFromPin(callPairsFromPin, "./thttpd/thttpd.pinout");

    for (const auto& P : callPairsFromPin){
      for (auto& E : CG){
	if (P.caller == E.caller && P.callee == E.callee){
	  E.call_times++;
	  //	  errs() << "Found runtime call " << E.caller << " " << E.callee << "\n";
	}
      }
    }

    string sourceFunc = "auth_check2";
    findEdgesWithImplicitLeak(CG, sourceFunc);
    set<string> S;
    for(auto const SF : PDG->senFuncs){
      S.insert(SF->getFunction()->getName());
    }
    
    findEdgesWithForwardLeak(CG, S);

    printCallGraphToFile(CG, "./thttpd/thttpd.callgraph");

    errs() << "CallPairsFromPin: " << callPairsFromPin.size() << "\n";

    int temp = 0;
    for(const auto& CP : callPairsFromPin){
      if ((funcSet.find(CP.caller) != funcSet.end()) &&
	  (funcSet.find(CP.callee) != funcSet.end()) ){
	temp++;
      }
    }
    errs() << "real callpairs: " << temp << "\n";


    //   printFidSizeSetToFile(fidSizeSet, "./thttpd_id_code_size.txt");
    //   printFidSizeSetToFile(fidSizeSet, "./ssh_id_code_size.txt");
    fidSizeSet.clear();
    callPairsFromPin.clear();
    errs() << "===============END GetCallGraph Pass runOnModule: ===============" << "\n";

    return false;
  }
};





char GetCallGraph::ID = 0;
static RegisterPass<GetCallGraph> GCG("get-call-graph", "Get Call Graph Pass",
				      false /* Only looks at CFG */,
				      false /* Analysis Pass */);




//      printCallSiteToFile(cswSet);
//      readCallSiteFromFile(cswSetFromFile, "CallSiteStat.txt");
//     errs() << "SetFromFile" << cswSetFromFile.size() << "\n";
/*
  for(auto const& E: cswSetFromFile){
  errs() << E->id << " " << E->func << " " << E->dir << " " << E->file << " " << E->line << " " << E->calltimes << "\n";
  }

  cswSetFromFile.clear();


  gcovDict.clear();
  cswSet.clear();
*/



#if 0
//auto scope = i->getDebugLoc().getScope(M->getContext())->getFileName();
MDNode *MDN = I.getMetadata("dbg");
DILocation loc(MDN);  

auto filename = loc.getFilename().str(); 
auto dir = loc.getDirectory().str();
auto line = loc.getLineNumber();
errs() << "in file: " << filename << " Line: " << line << "\n";

//get call times in the corresponding .c.gcov
string calltimespath = call_times_path + "/" + filename + ".gcov.in.calltimesonly";
errs() << "DEBUG:" << calltimespath << "\n";
//if defined in a header file, skip

if(existedFiles.find(calltimespath) == existedFiles.end()){
  errs() << "DEBUG: calltimespath:" << calltimespath << " cannot be found in repo, so skip\n";
  continue;
 }
		      
errs() << "call times at this loc: " << gcovDict[calltimespath][line-1] << "\n";
int ct = gcovDict[calltimespath][line-1];
CallSiteWrapper* CSW = new CallSiteWrapper(call_site_id, &I, callee->getName(), filename, dir, line, ct);
call_site_id++;
cswSet.insert(CSW);
errs() << "cswSet.size = " << cswSet.size() << "\n";
#endif



int readCallTimesFromFilesOld(const std::string& dir, 
			      map<string, vector<int> >& gcovDict)
{
  ifstream infile;
  string filepath;
  DIR *dp;
  struct dirent *dirp;
  struct stat filestat;

  errs() << "dir to get files of:" << dir << "\n";

  dp = opendir( dir.c_str() );
  if (dp == NULL){
    errs() << "Error(" << errno << ") opening " << dir << "\n";
    return errno;
  }

  while ((dirp = readdir( dp ))){
    filepath = dir + "/" + dirp->d_name;
    // If the file is a directory (or is in some way invalid) we'll skip it e.g. ("." "..")
    if (stat( filepath.c_str(), &filestat )) continue;
    if (S_ISDIR( filestat.st_mode ))         continue;
    errs() << "filepath: " << filepath << "\n";

    // Endeavor to read a single number from the file and display it
    infile.open( filepath.c_str() );
    if(!infile.is_open()){
      errs() << "Faile to open calltimes file: " << filepath << "\n";
      exit(1);
    }
    existedFiles.insert(filepath);

    vector<int> calltimes_for_this_file;
    int num;
    while(infile >> num){
      calltimes_for_this_file.push_back(num);
    }
    //map filepath to its calltimes vector in memory
    gcovDict[filepath] = calltimes_for_this_file;
    infile.close();
  }
  closedir( dp );
  return 0;
}


/*
  void printCallSiteToFile(set<CallSiteWrapper*>& S){
  ofstream outfile;
  outfile.open(call_site_stat);
  
  for(auto const &cs : S){
  //    outfile << cs->id " " << cs->inst->getParent()->getParent()->getName().str() << " " << cs->func << " " 
  //	    << cs->dir << " " << cs->file << " " << cs->line << " " << cs->calltimes << "\n";
  outfile << cs->inst->getParent()->getParent()->getName().str() << " " << cs->func << " " << cs->calltimes << "\n";
  }
  outfile.close();
  }
*/


//      errs() << "============================= Get Call Graph from the PDG ==================================\n";
/*     
       errs() << "============== Read call times from ***.c.gcov.calltimesonly files and record: ==============" << "\n";
       if (0 != readCallTimesFromFiles(call_times_path, gcovDict))
       errs() << "readCallTimesFromFiles failed...\n";

       errs() << "gcovDict size = " << gcovDict.size() << "\n";
*/
