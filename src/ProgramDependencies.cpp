
/** ---*- C++ -*--- ProgramDependencies.cpp
 *
 * Copyright (C) 2012 Marco Minutoli <mminutoli@gmail.com>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

#include "Config.h"

#include <unistd.h>

//#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/DebugInfo.h"


#include "llvm/Bitcode/ReaderWriter.h"

#include "ConnectFunctions.h"
#include "FunctionWrapper.h"
#include "ProgramDependencies.h"
#include "SystemDataDependencies.h"
#include "SystemControlDependenceGraph.h"

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
#include <map>
#include <vector>
#include <deque>
#include <list>
#include <iostream>
#include <fstream>

#include <string.h>
#include <time.h>


#define COUNT_INDIRECT_AND_SYS_CALL 1

using namespace std;
using namespace cot;
using namespace llvm;

typedef struct S{
  int val; 
  struct S* next;
}tnameS;

//unsigned getLine() const in DebugLoc.h
std::map<llvm::Value*, std::set<string> > privateMap;
//map each alloca into a status(bool), if true means this alloca now is sensitive,otherwise not

const unsigned allocaMAX = 100000;
//std::map<llvm::Instruction*, unsigned> allocaMap;
std::set<string> fixedPrivateValues;

char ProgramDependencyGraph::ID = 0;
//std::map<const llvm::BasicBlock *,BasicBlockWrapper *> BasicBlockWrapper::bbMap;
AliasAnalysis* ProgramDependencyGraph::Global_AA = nullptr;

std::map<const llvm::Function *,FunctionWrapper *> FunctionWrapper::funcMap;
std::map<const llvm::CallInst *,CallWrapper * > CallWrapper::callMap;



std::set<string> typeSet;

std::set<llvm::Value*> allPtrSet;
std::vector<llvm::Value*> sensitive_values;
std::vector<InstructionWrapper*> sensitive_nodes;

std::vector<pair<string, string> > edgesWithParamLeak;
std::vector<pair<string, string> > edgesWithReturnLeak;
// e.g. Key* load_identity_file (...), there should be an big leak number on the return edge 
std::vector<pair<string, string> > edgesWithPotentialLeakFromArgs; 
std::vector<pair<string, string> > edgesWithPotentialLeakFromRet;

void ProgramDependencyGraph::connectAllPossibleFunctions(InstructionWrapper* CInstW, FunctionType* funcTy){

  std::map<const llvm::Function *,FunctionWrapper *>::iterator FI =  FunctionWrapper::funcMap.begin();
  std::map<const llvm::Function *,FunctionWrapper *>::iterator FE =  FunctionWrapper::funcMap.end();

  for(; FI != FE; ++FI){
    if((*FI).first->getFunctionType() == funcTy && (*FI).first->getName() != "main"){
      ;
      //      Function* callee = (*FI).first;
      //      PDG->addDependency(*InstructionWrapper::nodes.find(CInstW), FunctionWrapper::funcMap[(*FI).first]->getEntry(), CONTROL);
      //    errs() << (*FI).first->getName() << " function pointer! \n";
      //TODO:
      //color a ret node in callee(func ptr)randomly as long as we can combine them together with caller
    }
  }
}

void ProgramDependencyGraph::drawFormalParameterTree(Function* func, TreeType treeTy){
  for(list<ArgumentWrapper*>::iterator argI = FunctionWrapper::funcMap[func]->getArgWList().begin(),
	argE = FunctionWrapper::funcMap[func]->getArgWList().end(); argI != argE; ++argI){
    for(tree<InstructionWrapper*>::iterator TI = (*argI)->getTree(treeTy).begin(), 
	  TE = (*argI)->getTree(treeTy).end(); TI != TE; ++TI){	      		      
      for(int i = 0; i < TI.number_of_children(); i++){
	InstructionWrapper *childW = *(*argI)->getTree(treeTy).child(TI, i);

	if(nullptr == *InstructionWrapper::nodes.find(*TI)) errs() << "DEBUG LINE 84 InstW NULL\n";
	if(nullptr == *InstructionWrapper::nodes.find(childW)) errs() << "DEBUG LINE 85 InstW NULL\n";

	PDG->addDependency(*InstructionWrapper::nodes.find(*TI), *InstructionWrapper::nodes.find(childW), PARAMETER);
      } 	      
    }//end for tree
  }//end for list
}

void ProgramDependencyGraph::drawActualParameterTree(CallInst* CI, TreeType treeTy){      
  for(list<ArgumentWrapper*>::iterator argI = CallWrapper::callMap[CI]->getArgWList().begin(),
	argE = CallWrapper::callMap[CI]->getArgWList().end(); argI != argE; ++argI){

    for(tree<InstructionWrapper*>::iterator TI = (*argI)->getTree(treeTy).begin(), 
	  TE = (*argI)->getTree(treeTy).end(); TI != TE; ++TI){	      		      
      for(int i = 0; i < TI.number_of_children(); i++){
	InstructionWrapper *childW = *(*argI)->getTree(treeTy).child(TI, i);

	if(nullptr == *InstructionWrapper::nodes.find(*TI)) errs() << "DEBUG LINE 103 InstW NULL\n";
	if(nullptr == *InstructionWrapper::nodes.find(childW)) errs() << "DEBUG LINE 104 InstW NULL\n";

	PDG->addDependency(*InstructionWrapper::nodes.find(*TI), *InstructionWrapper::nodes.find(childW), PARAMETER);
      } 	      
    }//end for tree
  }//end for list
}

void ProgramDependencyGraph::connectFunctionAndFormalTrees(llvm::Function *callee){
  for(list<ArgumentWrapper*>::iterator argI = FunctionWrapper::funcMap[callee]->getArgWList().begin(),
	argE = FunctionWrapper::funcMap[callee]->getArgWList().end(); argI != argE; ++argI){

    InstructionWrapper *formal_inW = *(*argI)->getTree(FORMAL_IN_TREE).begin();
    InstructionWrapper *formal_outW = *(*argI)->getTree(FORMAL_OUT_TREE).begin();

    //connect Function's EntryNode with formal in/out tree roots 
    PDG->addDependency(FunctionWrapper::funcMap[callee]->getEntry(), *InstructionWrapper::nodes.find(formal_inW), PARAMETER);
    PDG->addDependency(FunctionWrapper::funcMap[callee]->getEntry(), *InstructionWrapper::nodes.find(formal_outW), PARAMETER);

    //TODO: connect corresponding instructions with internal formal tree nodes
  
    //two things: (1) formal-in --> callee's Store; (2) callee's Load --> formal-out
    for(tree<InstructionWrapper*>::iterator formal_in_TI= (*argI)->getTree(FORMAL_IN_TREE).begin(),
	  formal_in_TE  = (*argI)->getTree(FORMAL_IN_TREE).end(), 
	  formal_out_TI = (*argI)->getTree(FORMAL_OUT_TREE).begin();
	formal_in_TI != formal_in_TE; ++formal_in_TI, ++formal_out_TI){

      //connect formal-in and formal-out nodes formal-in --> formal-out
      PDG->addDependency(*InstructionWrapper::nodes.find(*formal_in_TI), *InstructionWrapper::nodes.find(*formal_out_TI), PARAMETER);
    
      //must handle nullptr case first
      if(nullptr == (*formal_in_TI)->getFieldType() ){
	errs() << "connectFunctionAndFormalTrees: formal_in_TI->getFieldType() == nullptr !\n";
	break;
      }

      //connect formal-in-tree type nodes with storeinst in call_func, approximation used here
      if(nullptr != (*formal_in_TI)->getFieldType()){

	std::list<StoreInst*>::iterator SI = FunctionWrapper::funcMap[callee]->getStoreInstList().begin();
	std::list<StoreInst*>::iterator SE = FunctionWrapper::funcMap[callee]->getStoreInstList().end();

	for(;SI != SE; ++SI){
	  if((*formal_in_TI)->getFieldType() == (*SI)->getValueOperand()->getType()){
	    for(std::set<InstructionWrapper*>::iterator nodeIt = InstructionWrapper::nodes.begin();
		nodeIt != InstructionWrapper::nodes.end(); ++nodeIt){
	
	      if((*nodeIt)->getInstruction() == dyn_cast<Instruction>(*SI))
		PDG->addDependency(*InstructionWrapper::nodes.find(*formal_in_TI), *InstructionWrapper::nodes.find(*nodeIt), DATA_GENERAL);	      
	    }
	  }
	}//end for(;SI != SE; ++SI)
      }//end if nullptr == (*formal_in_TI)->getFieldType()

      //2. Callee's LoadInsts --> FORMAL_OUT in Callee function
      //must handle nullptr case first
      if(nullptr == (*formal_out_TI)->getFieldType() ){
	errs() << "connectFunctionAndFormalTrees: LoadInst->FORMAL_OUT: formal_out_TI->getFieldType() == nullptr!\n";
	break;
      }

      if(nullptr != (*formal_out_TI)->getFieldType()){

	std::list<LoadInst*>::iterator LI = FunctionWrapper::funcMap[callee]->getLoadInstList().begin();
	std::list<LoadInst*>::iterator LE = FunctionWrapper::funcMap[callee]->getLoadInstList().end();
      
	for(;LI != LE; ++LI){
	  if((*formal_out_TI)->getFieldType() == (*LI)->getPointerOperand()->getType()->getContainedType(0)){
	    for(std::set<InstructionWrapper*>::iterator nodeIt = InstructionWrapper::nodes.begin();
		nodeIt != InstructionWrapper::nodes.end(); ++nodeIt)
	
	      if((*nodeIt)->getInstruction() == dyn_cast<Instruction>(*LI))		
		PDG->addDependency(*InstructionWrapper::nodes.find(*nodeIt), *InstructionWrapper::nodes.find(*formal_out_TI), DATA_GENERAL);
	  }
	}//end for(; LI != LE; ++LI)
      }//end if(nullptr != (*formal_out_TI)->...)
    }//end for (tree formal_in_TI...)
  }//end for arg iteration...
}


int ProgramDependencyGraph::connectCallerAndCallee(InstructionWrapper *InstW, llvm::Function *callee){

  if(InstW == nullptr || callee == nullptr)
    return 1;
  
  //#if PARAMETER_TREE
  //callInst in caller --> Entry Node in callee
  PDG->addDependency(InstW, FunctionWrapper::funcMap[callee]->getEntry(), CONTROL);
  //#else
  //  PDG->addDependency(InstW, FunctionWrapper::funcMap[callee]->getEntry(), DATA_GENERAL);
  //#endif
  
  //ReturnInst in callee --> CallInst in caller
  Instruction* RI = nullptr;
  for(auto &B : *callee){
    for(auto &I : B)
      if(isa<ReturnInst>(I))
	RI = &I; 
  }

  if (callee->getName() == "auth_check"){
    errs() << "when callee is auth_check, RI: " << *RI;
    errs() << "CI is: " << *InstW->getInstruction() << " caller: " << InstW->getFunction()->getName() << "\n";
  }

  // If this ReturnInst not in nodes yet, insert first
  /*
    if(InstructionWrapper::instMap.find(RI) == InstructionWrapper::instMap.end()){
    InstructionWrapper *iw = new InstructionWrapper(RI, InstW->getFunction(), INST);
    InstructionWrapper::nodes.insert(iw);
    InstructionWrapper::instMap[RI] = iw;
    InstructionWrapper::funcInstWList[InstW->getFunction()].insert(iw);
    }
  */
  for(std::set<InstructionWrapper*>::iterator nodeIt = InstructionWrapper::nodes.begin();
      nodeIt != InstructionWrapper::nodes.end(); ++nodeIt){
	
    if((*nodeIt)->getInstruction() == RI){
      if (nullptr != dyn_cast<ReturnInst>((*nodeIt)->getInstruction())->getReturnValue()){
	PDG->addDependency(*InstructionWrapper::nodes.find(*nodeIt), InstW, RET);
	if (callee->getName() == "auth_check")
	  errs() << "auth_check ReturnInst : " << *RI << "InstW is in " << InstW->getFunction()->getName() << "\n";
	if (callee->getName() == "auth_check2")
	  errs() << "auth_check2 ReturnInst size: " << *RI << "\n";
      }
      //TODO: indirect call, function name??
      else 
	;// errs() << "void ReturnInst: " << *(*nodeIt)->getInstruction() << " Function: " << callee_func->getName();
    }
  }
  
#if PARAMETER_TREE

  //TODO: consider all kinds of connecting cases
  //connect caller InstW with ACTUAL IN/OUT parameter trees
  CallInst *CI = dyn_cast<CallInst>(InstW->getInstruction());

  for(list<ArgumentWrapper*>::iterator argI = CallWrapper::callMap[CI]->getArgWList().begin(),
	argE = CallWrapper::callMap[CI]->getArgWList().end(); argI != argE; ++argI){

    InstructionWrapper *actual_inW = *(*argI)->getTree(ACTUAL_IN_TREE).begin();
    InstructionWrapper *actual_outW = *(*argI)->getTree(ACTUAL_OUT_TREE).begin();

    if(nullptr == *InstructionWrapper::nodes.find(actual_inW)) errs() << "DEBUG LINE 168 InstW NULL\n";
    if(nullptr == *InstructionWrapper::nodes.find(actual_outW)) errs() << "DEBUG LINE 169 InstW NULL\n";

    PDG->addDependency(InstW, *InstructionWrapper::nodes.find(actual_inW), PARAMETER);
    PDG->addDependency(InstW, *InstructionWrapper::nodes.find(actual_outW), PARAMETER);    
  }

  //old way, process four trees at the same time, remove soon
  list<ArgumentWrapper*>::iterator formal_argI = FunctionWrapper::funcMap[callee]->getArgWList().begin();
  list<ArgumentWrapper*>::iterator formal_argE = FunctionWrapper::funcMap[callee]->getArgWList().end();

  list<ArgumentWrapper*>::iterator actual_argI = CallWrapper::callMap[CI]->getArgWList().begin();
  list<ArgumentWrapper*>::iterator actual_argE = CallWrapper::callMap[CI]->getArgWList().end();

  //increase formal/actual tree iterator simutaneously
  for(; formal_argI != formal_argE; ++formal_argI, ++actual_argI){
    //intra-connection between ACTUAL/FORMAL IN/OUT trees
    for(tree<InstructionWrapper*>::iterator actual_in_TI= (*actual_argI)->getTree(ACTUAL_IN_TREE).begin(),
	  actual_in_TE  = (*actual_argI)->getTree(ACTUAL_IN_TREE).end(), 
	  formal_in_TI  = (*formal_argI)->getTree(FORMAL_IN_TREE).begin(), //TI2
	  formal_out_TI = (*formal_argI)->getTree(FORMAL_OUT_TREE).begin(), //TI3
	  actual_out_TI = (*actual_argI)->getTree(ACTUAL_OUT_TREE).begin();  //TI4
	actual_in_TI != actual_in_TE; ++actual_in_TI, ++formal_in_TI, ++formal_out_TI, ++actual_out_TI){

      //connect trees: antual-in --> formal-in, formal-out --> actual-out
      PDG->addDependency(*InstructionWrapper::nodes.find(*actual_in_TI), *InstructionWrapper::nodes.find(*formal_in_TI), PARAMETER);
      PDG->addDependency(*InstructionWrapper::nodes.find(*formal_out_TI), *InstructionWrapper::nodes.find(*actual_out_TI), PARAMETER);
       
    }//end for(tree...) intra-connection between actual/formal

    //TODO: why removing this debugging infor will cause segmentation fault?
 
    //3. ACTUAL_OUT --> LoadInsts in #Caller# function
    for(tree<InstructionWrapper*>::iterator actual_out_TI = (*actual_argI)->getTree(ACTUAL_OUT_TREE).begin(),
	  actual_out_TE = (*actual_argI)->getTree(ACTUAL_OUT_TREE).end(); actual_out_TI != actual_out_TE; ++actual_out_TI){

      //must handle nullptr case first
      if(nullptr == (*actual_out_TI)->getFieldType() ){
	errs() << "DEBUG ACTUAL_OUT->LoadInst: actual_out_TI->getFieldType() is empty!\n";
	break;
      }

      if(nullptr != (*actual_out_TI)->getFieldType()){

	std::list<LoadInst*>::iterator LI = FunctionWrapper::funcMap[InstW->getFunction()]->getLoadInstList().begin();
	std::list<LoadInst*>::iterator LE = FunctionWrapper::funcMap[InstW->getFunction()]->getLoadInstList().end();
      
	for(;LI != LE; ++LI){
	  if((*actual_out_TI)->getFieldType() == (*LI)->getType()){
	    for(std::set<InstructionWrapper*>::iterator nodeIt = InstructionWrapper::nodes.begin();
		nodeIt != InstructionWrapper::nodes.end(); ++nodeIt){
	
	      if((*nodeIt)->getInstruction() == dyn_cast<Instruction>(*LI))
		PDG->addDependency(*InstructionWrapper::nodes.find(*actual_out_TI), *InstructionWrapper::nodes.find(*nodeIt), DATA_GENERAL);
	    }
	  }
	}//end for(; LI != LE; ++LI)
      }//end if(nullptr != (*TI3)->...)
    }// end for(tree actual_out_TI = getTree FORMAL_OUT_TREE)     

  }//end for argI iteration

  //end if PARAMETER_TREE
#endif

  return 0;
}


void ProgramDependencyGraph::FindGlobalsInReadAndWrite(InstructionWrapper* InstW,
						       map<Value*, set<Function*> >& globalTaintedFuncMap){
  Instruction *I = InstW->getInstruction();
  if(I == nullptr){
    errs() << "Wrong input in FindGlobalsInReadAndWrite\n";
    exit(1);
  }

  // process GetElementPtr 1. GetElementPtr 2. Load 3. Store
  if(InstW->getType() == INST && !InstW->getAccess())
    {
      if(isa<GetElementPtrInst>(I)){
	GetElementPtrInst* GPI = dyn_cast<GetElementPtrInst>(I); 
	if(isa<GlobalVariable>(GPI->getPointerOperand())){
	  //  errs() << "GLOBAL_in_GetElementptrInst: " << *I<< "\n";
	  //  errs() << "ptr: " << *GPI->getPointerOperand() << "\n" << "is a GlobalVariable\n";
	  GlobalVariable *gv = dyn_cast<GlobalVariable>(GPI->getPointerOperand());
	  if (!gv->isConstant())
	    globalTaintedFuncMap[GPI->getPointerOperand()].insert(InstW->getFunction());
	}
	InstW->setAccess(true);
      }
      if(isa<LoadInst>(I)){
	LoadInst* LI = dyn_cast<LoadInst>(I);
	Value* ptr = LI->getPointerOperand();
	GEPOperator* gop = dyn_cast<GEPOperator>(ptr);
	if(gop != nullptr && isa<GlobalVariable>(gop->getPointerOperand())){
	  // errs() << "GEPOperator(load): " << *gop << "\n" << "is a GEPOperator\n";
	  // errs() << "GLOBAL_in_GEPOperator: " << *gop->getPointerOperand() << "\n";
	  GlobalVariable *gv = dyn_cast<GlobalVariable>(gop->getPointerOperand());
	  if (!gv->isConstant())
	    globalTaintedFuncMap[gop->getPointerOperand()].insert(InstW->getFunction());		  
	}
	InstW->setAccess(true);
      }
      if(isa<StoreInst>(I)){
	StoreInst* SI = dyn_cast<StoreInst>(I);
	Value* ptr = SI->getPointerOperand();
	GEPOperator* gop = dyn_cast<GEPOperator>(ptr);
	if(gop != nullptr && isa<GlobalVariable>(gop->getPointerOperand())){
	  // errs() << "GEPOperator(store): " << *gop << "\n" << "is a GEPOperator\n";
	  // errs() << "GLOBAL_in_GEPOperator: " << *gop->getPointerOperand() << "\n";
	  GlobalVariable *gv = dyn_cast<GlobalVariable>(gop->getPointerOperand());
	  if (!gv->isConstant())
	    globalTaintedFuncMap[gop->getPointerOperand()].insert(InstW->getFunction());		  
	}
	InstW->setAccess(true);
      }	      
    }
  return;
}

// define internal void @httpd_realloc_str(i8** %strP, i64* %maxsizeP, i64 %size) 
// store i8** %strP, i8*** %strP.addr, align 8
// call void @llvm.dbg.declare(metadata !{i8*** %strP.addr}, metadata !3455), !dbg !3456
// store i64* %maxsizeP, i64** %maxsizeP.addr, align 8
void processStoredArgument(Function* F, map<Value*, Value*>& ParamArgMap){
  int count = ParamArgMap.size();
    for (BasicBlock &B : *F){
      for (Instruction &I : B){
	if (isa<StoreInst>(&I)){
	  StoreInst* SI = dyn_cast<StoreInst>(&I);
	  if (ParamArgMap.find(SI->getValueOperand()) != ParamArgMap.end()){
	    //	    errs() << "Arg stored into temp Reg\n";
	    //	    errs() << "Arg: " << *SI->getValueOperand() << " | Reg: " << *SI->getPointerOperand() << "\n";
	    ParamArgMap[SI->getPointerOperand()] = ParamArgMap[SI->getValueOperand()];
	  }
	}
      }
    }
    /*
    if(ParamArgMap.size() != count){
            errs() << "ParamArgMap size changed to: " << ParamArgMap.size() << "\n";
      for (auto const&I : ParamArgMap){
	errs() << " key: " << *I.first << " | " << *I.second << "\n"; 
      }
    }
    */
    return;
}

void ProgramDependencyGraph::FindGlobalsInCalleeFunction(Function* F, 
							 map<Value*, Value*>& ParamArgMap,
							 map<Value*, set<Function*> >& globalTaintedFuncMap){
  if (ParamArgMap.empty()){
    errs() << "No need to find globals because ParamArgMap is empty!\n";
    exit(1);
  }

  processStoredArgument(F, ParamArgMap);

  for (BasicBlock &B : *F){
    for (Instruction &I : B){
      if (isa<LoadInst>(&I)){
	LoadInst* LI = dyn_cast<LoadInst>(&I);
	Value* ptr = LI->getPointerOperand();
	if (ptr != nullptr && ParamArgMap.find(ptr) != ParamArgMap.end()){
	  // errs() << "READ Gloabl-arg found in " << F->getName() << "\n";
	  // errs() << "Arg is : " << *ptr << "\n";
	  // errs() << "Real Global: " << *ParamArgMap[ptr] << "\n";
	  globalTaintedFuncMap[ParamArgMap[ptr]].insert(F);	  
	}
      }

      if(isa<StoreInst>(&I)){
	StoreInst* SI = dyn_cast<StoreInst>(&I);
	Value* ptr = SI->getPointerOperand();
	if (ptr != nullptr && ParamArgMap.find(ptr) != ParamArgMap.end()){
	  // errs() << "WRITE Global-arg found in " << F->getName() << "\n";
	  // errs() << "Arg is : " << *ptr << "\n";
	  // errs() << "Real Global: " << *ParamArgMap[ptr] << "\n";
	  globalTaintedFuncMap[ParamArgMap[ptr]].insert(F);
	}
      }
    }
  }// end for
  return;
}

string getTypeName(Type* ty){
  if (ty == nullptr){
    errs() << "getTypeName null ptr input!\n";
    exit(1);
  }
  string type_str;
  raw_string_ostream rso(type_str);
  rso << *ty;

  return rso.str();
}


std::set<string> systemcallSet;
void readSystemCallTableFromFile(set<string>& S, string filename){
  ifstream infile(filename);
  string line;
 
  if (!infile.is_open()){
    errs() << "Fail to read CallSite, file can't be opened!\n ";
    exit(0);
  }

  while(infile >> line)
    S.insert(line);  
}

std::set<string> senFuncSet;
void readSensitiveFuncsFromFile(set<string>& S, string filename){
  ifstream infile(filename);
  string line;
 
  if (!infile.is_open()){
    errs() << "Fail to read CallSite, file can't be opened!\n ";
    exit(0);
  }

  while(infile >> line)
    S.insert(line);  
}




bool ProgramDependencyGraph::runOnModule(Module &M)
{
  Global_AA = &getAnalysis<AliasAnalysis>();
  errs() << "ProgramDependencyGraph::runOnModule" << '\n';
  FunctionWrapper::constructFuncMap(M);
  errs() << "funcMap size = " << FunctionWrapper::funcMap.size() << '\n';

#if COUNT_INDIRECT_AND_SYS_CALL
  int indirect_call_count = 0;
  int system_call_count = 0;
  int sensitive_indirect_call_count = 0;
  int sensitive_system_call_count = 0;	
  ofstream indirect_call_file;
  ofstream system_call_file;
  indirect_call_file.open("indirect_calls.txt");
  system_call_file.open("system_calls.txt");

  readSystemCallTableFromFile(systemcallSet, "linux_syscall_table.txt");
  errs() << "systemcallSet size:" << systemcallSet.size() << "\n";

  readSensitiveFuncsFromFile(senFuncSet, "sensitive_functions.txt");
  errs() << "senFuncSet size:" << senFuncSet.size() << "\n";

#endif

  // Type preprocessing
    TypeFinder allTypes;
    allTypes.run(M, true);
    errs() << "======================================= Type List BEGIN ====================================\n";
    for (auto *ty : allTypes){
      string type_str;
      raw_string_ostream rso(type_str);
      rso << *ty;
      typeSet.insert(rso.str());
      errs() << rso.str() << "\n";
    }
    errs() << "typeSet size: " << typeSet.size() << "\n";
    errs() << "======================================= Type List END ====================================\n";



  //Get the Module's list of global variable and function identifiers  
  errs()<<"======Global List: ======\n";

  for(llvm::Module::global_iterator globalIt = M.global_begin(); globalIt != M.global_end(); ++globalIt){
    InstructionWrapper *globalW = new InstructionWrapper(nullptr, nullptr, &(*globalIt), GLOBAL_VALUE);
    InstructionWrapper::nodes.insert(globalW);
    InstructionWrapper::globalList.insert(globalW);
    
    //find all global pointer values and insert them into a list
    if(globalW->getValue()->getType()->getContainedType(0)->isPointerTy())
      gp_list.push_back(globalW);

    // immutable global, e.g. @str = "printf..."
    if ((*globalIt).isConstant())
      continue;
    
    else{
      if (((*globalIt).hasInitializer())){
	ConstantExpr *CE = dyn_cast<ConstantExpr>((*globalIt).getInitializer());
	// we use isGEPWithNoNotionalOverIndexing to capture an global like:
	// @err302form = internal global i8* getelementptr inbounds ([28 x i8]* @.str522, i32 0, i32 0), align 8
	if (CE != nullptr && CE->isGEPWithNoNotionalOverIndexing())
	  continue;
      }
      //      errs() << "mutable global: " << *globalW->getValue() << "\n";
      InstructionWrapper::nonConstantGlobalList.insert(globalW);
    }
  }

  int funcs = 0;
  int colored_funcs = 0;
  int uncolored_funcs = 0;

  for(Module::iterator F = M.begin(), E = M.end(); F != E; ++F){
    if((*F).isDeclaration())
      continue;
      
    InstructionWrapper::constructInstMap(*F);
  }

  //process a module function by function
  for(Module::iterator F = M.begin(), E = M.end(); F != E; ++F)
    {
      if((*F).isDeclaration())
	continue;
      
      if((*F).getName() == "crypto_hashblocks_sha512"){
	errs() << "crypto_hashblocks_sha512 is too tricky to be processed, bypass for simplicity!\n";
	continue;
      }

      funcs++;//label this author-defined function
      errs() << "PDG " << 1.0*funcs/M.getFunctionList().size()*100 << "% completed\n";

      //find all Load/Store instructions for each F, insert to F's storeInstList and loadInstList
      for(inst_iterator I = inst_begin(F), IE = inst_end(F); I != IE; ++I){
	Instruction *pInstruction = dyn_cast<Instruction>(&*I);
	if(isa<StoreInst>(pInstruction)){
	  StoreInst* SI = dyn_cast<StoreInst>(pInstruction);
	  FunctionWrapper::funcMap[&*F]->getStoreInstList().push_back(SI);
	  FunctionWrapper::funcMap[&*F]->getPtrSet().insert(SI->getPointerOperand());
	  if(SI->getValueOperand()->getType()->isPointerTy())
	    FunctionWrapper::funcMap[&*F]->getPtrSet().insert(SI->getValueOperand());
	} 
	if(isa<LoadInst>(pInstruction)){
	  LoadInst* LI = dyn_cast<LoadInst>(pInstruction);
	  FunctionWrapper::funcMap[&*F]->getLoadInstList().push_back(LI);
	  FunctionWrapper::funcMap[&*F]->getPtrSet().insert(LI->getPointerOperand());
	}
	if(isa<ReturnInst>(pInstruction))
	  FunctionWrapper::funcMap[&*F]->getReturnInstList().push_back(pInstruction);
		
	if(isa<CallInst>(pInstruction))
	  FunctionWrapper::funcMap[&*F]->getCallInstList().push_back(dyn_cast<CallInst>(pInstruction));		  	      
	if(isa<AllocaInst>(pInstruction)){
	  AllocaInst* AI = dyn_cast<AllocaInst>(pInstruction);
	  if(AI->getName().find("retval") == string::npos)
	    FunctionWrapper::funcMap[&*F]->getAllocaMap()[pInstruction] = allocaMAX;
	}
      }
      //print PtrSet only

      DataDependencyGraph &ddgGraph = getAnalysis<DataDependencyGraph>(*F);
      ControlDependencyGraph &cdgGraph = getAnalysis<ControlDependencyGraph>(*F);
      cdgGraph.computeDependencies(*F, cdgGraph.PDT);

      //set Entries for Function, set up links between dummy entry nodes and their func*
      for(std::set<InstructionWrapper*>::iterator nodeIt = InstructionWrapper::funcInstWList[&*F].begin();
	  nodeIt != InstructionWrapper::funcInstWList[&*F].end(); ++nodeIt){
	InstructionWrapper *InstW = *nodeIt;
	if(InstW->getType() == ENTRY){
	  std::map<const llvm::Function *,FunctionWrapper *>::const_iterator FI = 
	    FunctionWrapper::funcMap.find(InstW->getFunction()); 
	  if(FI != FunctionWrapper::funcMap.end()){
	    //   errs() << "find successful!" << "\n";
	    FunctionWrapper::funcMap[InstW->getFunction()]->setEntry(InstW);
	  }   
	}
      }//end for set Entries...

      clock_t begin2 = clock();

      //the iteration should be done for the instMap, not original F
      for(std::set<InstructionWrapper*>::iterator nodeIt = InstructionWrapper::funcInstWList[&*F].begin();
	  nodeIt != InstructionWrapper::funcInstWList[&*F].end(); ++nodeIt)
	{
	  InstructionWrapper *InstW = *nodeIt;
	  Instruction *pInstruction = InstW->getInstruction();

	  //process call nodes, one call node will only be touched once(!InstW->getAccess)
	  if (pInstruction != nullptr && InstW->getType() == INST && isa<CallInst>(pInstruction) && !InstW->getAccess())
	    {
	      InstructionWrapper *CallInstW = InstW;
	      CallInst *CI = dyn_cast<CallInst>(pInstruction);
	      Function *callee = CI->getCalledFunction();

	      //if this is an indirect function invocation(function pointer, member function...)
	      // e.g.   %1 = load i32 (i32)** %p, align 8
	      //	%call = call i32 %1(i32 2))
	      if (callee == nullptr){
		Type* t = CI->getCalledValue()->getType();

#if COUNT_INDIRECT_AND_SYS_CALL
		errs() << "indirect call:" << " " << indirect_call_count << " " << *t << "\n";
		
		string fname = InstW->getFunction()->getName().str();
                errs() << "fname:" << fname << "\n";
		if (senFuncSet.find(fname) != senFuncSet.end()){
                        errs() << "sen_func(for indirect_call):"<< fname << "\n";
			errs() << "sensitive_indirect_call:" << sensitive_indirect_call_count++ << "\n";
		}

		indirect_call_file << "indirect_call" << " " << indirect_call_count++  << "\n"; 

#endif

		FunctionType* funcTy = cast<FunctionType>(cast<PointerType>(t)->getElementType());
		errs() << "after cast<FunctionType>, ft = " << *funcTy <<"\n";
		connectAllPossibleFunctions(InstW, funcTy);
		continue;
	      }

	      //TODO: isIntrinsic or not? Consider intrinsics as common instructions for now, continue directly  
	      if (callee->isIntrinsic() || callee->isDeclaration()){

		if(systemcallSet.find(callee->getName().str()) != systemcallSet.end()){
			errs() << "syscall: " << callee->getName() << " count:" << system_call_count++ << "\n";
			string fname = InstW->getFunction()->getName().str();
//	                errs() << "fname:" << fname << "\n";
			if(senFuncSet.find(fname) != senFuncSet.end()){
				errs() << "sen_func(for syscall):"<< fname << "\n";
				errs() << "sensitive_syscall:" << callee->getName().str() << " " << sensitive_system_call_count++ << "\n";
			}

		}

		//if it is a var_annotation, save the sensitive value by the way
		if (callee->getIntrinsicID() == Intrinsic::var_annotation){
		  Value* v = CI->getArgOperand(0);
		  errs() << "Intrinsic var_annotation: " << *v << "\n";

		  if (isa<BitCastInst>(v)){
		    Instruction *tempI = dyn_cast<Instruction>(v);
		    errs() << "******** BitInst opcode: " << *tempI << "BitCast \n";

		    for (llvm::Use &U : tempI->operands()){
		      Value *v_for_cast = U.get();
		      sensitive_values.push_back(v_for_cast);
		      //		      inst_src_dict[v_for_cast] = tempI->getDebugLoc().getLine();
		    }
		  }
		  else
		    sensitive_values.push_back(v);
		}		  
		continue;
	      }

	      //TODO: tail call processing
	      if(CI->isTailCall())
		continue;
	      
	      //special cases done, common function
	      CallWrapper *callW = new CallWrapper(CI);
	      CallWrapper::callMap[CI] = callW;
	     
	      //take recursive callInst as common callInst
	      if(0 == connectCallerAndCallee(InstW, callee))
		InstW->setAccess(true);
	      
	      // check retval, if has sshkey, add potential leak from callee -> caller
	      string retTyName = getTypeName(callee->getFunctionType()->getReturnType());
	      if (retTyName.find("sshkey") != string::npos){
		errs() << "Ret has potential leak : " << *CI << "\n";
		errs() << callee->getName() << " --> " << InstW->getFunction()->getName() << "\n";
		edgesWithPotentialLeakFromRet.push_back(make_pair(callee->getName(), InstW->getFunction()->getName()));
	      }
	      
	      // common callee function, see if there is global variable in the CallInst's arg list
	      int argNum = CI->getNumArgOperands();	      
	      map<Value*, Value*> ParamArgMap;
	      for(int i = 0; i < argNum; i++){
		Value* argi = CI->getArgOperand(i);
		string tyName = getTypeName(argi->getType());
		// this arg has a sshkey type member, add potential leak <caller -> callee>
		  if (tyName.find("sshkey") != string::npos){
                      errs() << "potential leak CI : " << *CI << "\n";
                      errs() << InstW->getFunction()->getName() << " --> " << callee->getName() << "\n";
		      edgesWithPotentialLeakFromArgs.push_back(make_pair(InstW->getFunction()->getName(), callee->getName()));
                  }
		if (isa<GlobalVariable>(argi)){
		  globalTaintedFuncMap[argi].insert(InstW->getFunction());	
		  // go to callee function body
		  int j = 0;
		  for(Function::arg_iterator ai = CI->getCalledFunction()->arg_begin(); 
		      ai != CI->getCalledFunction()->arg_end(); ++ai){
		    if(j == i){
		      ParamArgMap[ai] = argi;
		    }
		    j++;
		  }
		}
	      }
	      //	      errs() << "ParamArgMap size: " << ParamArgMap.size() << "\n";
	      if (!ParamArgMap.empty())
		FindGlobalsInCalleeFunction(CI->getCalledFunction(), ParamArgMap, globalTaintedFuncMap);
	      // for CallInst we need to handle the arglist specially, to deal with related globals
	    }//end callnode
	  if(pInstruction != nullptr)
	    FindGlobalsInReadAndWrite(InstW, globalTaintedFuncMap);

	  //second iteration on nodes to add both control and data Dependency
	  for(std::set<InstructionWrapper*>::iterator nodeIt2 = InstructionWrapper::funcInstWList[&*F].begin();
	      nodeIt2 != InstructionWrapper::funcInstWList[&*F].end(); ++nodeIt2){
	    InstructionWrapper *InstW2 = *nodeIt2;
	    //process all non constant globals see whether dependency exists
	    if(InstW2->getType() == INST && isa<LoadInst>(InstW2->getInstruction())){
	      LoadInst* LI2 = dyn_cast<LoadInst>(InstW2->getInstruction());
	      for(std::set<InstructionWrapper *>::const_iterator gi = InstructionWrapper::nonConstantGlobalList.begin(); 
		  gi != InstructionWrapper::nonConstantGlobalList.end(); ++gi){	   
		if(LI2->getPointerOperand() == (*gi)->getValue()){
		  PDG->addDependency(*gi, InstW2, GLOBAL_VALUE);
		  globalTaintedFuncMap[(*gi)->getValue()].insert(InstW2->getFunction());
		}		
	      }// end searching globalList
	    }//end processing load for global

	    if (InstW2->getType() == INST && isa<StoreInst>(InstW2->getInstruction())){
	      StoreInst* SI2 = dyn_cast<StoreInst>(InstW2->getInstruction());
	      for(std::set<InstructionWrapper *>::const_iterator gi = InstructionWrapper::nonConstantGlobalList.begin(); 
		  gi != InstructionWrapper::nonConstantGlobalList.end(); ++gi){	   
		if(SI2->getPointerOperand() == (*gi)->getValue()){
		  // TODO: maybe some circles?
		  PDG->addDependency(*gi, InstW2, GLOBAL_VALUE);
		  globalTaintedFuncMap[(*gi)->getValue()].insert(InstW2->getFunction());
		}		
	      }// end searching globalList
	    }// end processing store to global

	    if(InstW->getType() == INST){	       
	      if (ddgGraph.DDG->depends(InstW, InstW2)) {
		//only StoreInst->LoadInst edge can be annotated
		if(InstW2->getType() == INST 
		   && isa<StoreInst>(InstW->getInstruction())
		   && isa<LoadInst>(InstW2->getInstruction())){
		  PDG->addDependency(InstW, InstW2, DATA_RAW);
		}
		else
		  PDG->addDependency(InstW, InstW2, DATA_DEF_USE);
	      }
	    
	      if(nullptr != InstW2->getInstruction()){		  
		if (cdgGraph.CDG->depends(InstW, InstW2)) 
		  PDG->addDependency(InstW, InstW2, CONTROL);
	      }
	    }//end if(InstW->getType()== INST)

	    if(InstW->getType() == ENTRY){
	      if (nullptr != InstW2->getInstruction() && cdgGraph.CDG->depends(InstW, InstW2))
		PDG->addDependency(InstW, InstW2, CONTROL);
	    }	    
	  }//end second iteration for PDG->addDependency...
	} //end the iteration for finding CallInst     	
    }//end for(Module...

  //print PtrSet only
  //  #if 0

  errs() << "\n\n PDG construction completed! ^_^\n\n";
  errs() << "funcs = " << funcs << "\n";

  errs() << "total syscall:" << system_call_count << "\n";
  errs() << "sensitive :" << sensitive_system_call_count << "\n";

  errs() << "total indirect_call:" << indirect_call_count << "\n";
  errs() << "sensitive :" << sensitive_indirect_call_count << "\n";

  errs() << "+++++++++++++++++++++++++++++++++++++++++++++\n";

  std::set<llvm::GlobalValue*> senGlobalSet;
  std::set<llvm::Instruction*> senInstSet;
  
  std::set<InstructionWrapper *>::const_iterator gi = InstructionWrapper::globalList.begin();
  std::set<InstructionWrapper *>::const_iterator ge = InstructionWrapper::globalList.end();

  errs() << "globalList.size = " << InstructionWrapper::globalList.size() << "\n";
  
  std::set<Function*> async_funcs;

  //sensitive global values(with annotations) can be directly get through Module.getNamedGlobal(GetNameGlobal in 3.9)
  auto global_annos = M.getNamedGlobal("llvm.global.annotations");
  if (global_annos){
    auto casted_array = cast<ConstantArray>(global_annos->getOperand(0));
    for (int i = 0; i < casted_array->getNumOperands(); i++) {
      auto casted_struct = cast<ConstantStruct>(casted_array->getOperand(i));
      if (auto sen_gv = dyn_cast<GlobalValue>(casted_struct->getOperand(0)->getOperand(0))) {
	auto anno = cast<ConstantDataArray>(cast<GlobalVariable>(casted_struct->getOperand(1)->getOperand(0))->getOperand(0))->getAsCString();
	if (anno == "sensitive") { 
	  errs() << "sensitive global found! value = " << *sen_gv << "\n";
	  senGlobalSet.insert(sen_gv);
	}
      }

      //TODO: rewrite these code to make it work for our function annotation
      if (auto fn = dyn_cast<Function>(casted_struct->getOperand(0)->getOperand(0))) {
	auto anno = cast<ConstantDataArray>(cast<GlobalVariable>(casted_struct->getOperand(1)->getOperand(0))->getOperand(0))->getAsCString();

	if (anno == "sensitive") { 
	  async_funcs.insert(fn);
	  errs() << "async_funcs ++ sensitive " << fn->getName() << "\n";
	}
      }// end if (auto...
    }// end for (int i ...
  }//end if (global_annos)


  set<string> leakFuncNames;
  // telnet
  /*
  leakFuncNames.insert("ring_supplied");
  leakFuncNames.insert("ring_empty_count");
  leakFuncNames.insert("willoption");
  leakFuncNames.insert("dooption");
  leakFuncNames.insert("telrcv");
  leakFuncNames.insert("printoption");
  */

  // wget
  /* 
  leakFuncNames.insert("sockaddr_set_data");
  leakFuncNames.insert("connect_to_ip");
  leakFuncNames.insert("ftp_expected_bytes");
  leakFuncNames.insert("print_length");
  leakFuncNames.insert("getftp");
  leakFuncNames.insert("ftp_response");
  leakFuncNames.insert("ftp_greeting");
  leakFuncNames.insert("ftp_login");
  leakFuncNames.insert("ftp_pasv");
  leakFuncNames.insert("ftp_type");
  leakFuncNames.insert("ftp_retr");
  leakFuncNames.insert("ftp_syst");
  leakFuncNames.insert("ftp_pwd");
  leakFuncNames.insert("ftp_size");
  leakFuncNames.insert("saved_append_1");
  leakFuncNames.insert("saved_append");
  leakFuncNames.insert("progress_create");
  leakFuncNames.insert("bar_create");
  leakFuncNames.insert("bar_update");
  leakFuncNames.insert("bar_finish");
  leakFuncNames.insert("count_cols");
  leakFuncNames.insert("create_image");
  leakFuncNames.insert("fd_read_body");
  leakFuncNames.insert("human_readable");
  leakFuncNames.insert("number_to_string");
  leakFuncNames.insert("number_to_static_string");
  */

  errs() << "chage sensitive functions added!\n";
  leakFuncNames.insert("get_defaults");
  leakFuncNames.insert("update_age");


  //process all sensitive instructions in functions and all global values, color their corresponding nodes in set "nodes"   
  for(std::set<InstructionWrapper*>::iterator nodeIt = InstructionWrapper::nodes.begin();
      nodeIt != InstructionWrapper::nodes.end(); ++nodeIt){
    InstructionWrapper *InstW = *nodeIt;
    Instruction *pInstruction = InstW->getInstruction();

    // put F's ReturnInst into sentitive nodes, if F is in leakFuncNames(Implicit)
    if (pInstruction != nullptr && isa<ReturnInst>(pInstruction)){
      string func = InstW->getFunction()->getName();
      if (leakFuncNames.find(func) != leakFuncNames.end()){
	errs() << "leak func: " << func << " ReturnInst: " << *pInstruction << "\n";
	sensitive_nodes.push_back(InstW);
      }
    }

    //process annoatated sensitive values(actually are instructionWrappers) in functions
    for(int i = 0; i < sensitive_values.size(); i++){
      if(sensitive_values[i] == pInstruction)
	sensitive_nodes.push_back(InstW); 
    }
    //based on senGloabalSet, find annotated global InstructionWrappers
    if(InstW->getType() == GLOBAL_VALUE){
      GlobalValue *gv = dyn_cast<GlobalValue>(InstW->getValue());
      //if gv is sensitive(inside senGlobalSet)
      if(senGlobalSet.end() != senGlobalSet.find(gv)){
	sensitive_nodes.push_back(InstW);
      }//end judging gv's sensitivity
    }//end global value
  }
 
  /*
    for(auto const &I : sensitive_nodes){
    errs() << "SENSITIVE NODE: " <<*I->getInstruction()<< "\n" ;    
    }
  */
  std::deque<const InstructionWrapper*> queue;
  for(int i = 0; i < sensitive_nodes.size(); i++){
    queue.push_back(sensitive_nodes[i]);
  }

  std::set<InstructionWrapper* > coloredInstSet;

  std::set<Function*> visitedF;

  //worklist algorithm for propagation
  while(!queue.empty()){ 
    InstructionWrapper *InstW = const_cast<InstructionWrapper*>(queue.front());
    if(InstW->getType() == INST)
      FunctionWrapper::funcMap[InstW->getFunction()]->setVisited(true); 

    queue.pop_front();
    //TODO: getInstruction should be removed  later, only for testing here temporarily
    //    errs() << "DEBUG: queue.size = " << queue.size() << "\n";
    if(InstW->getValue() == nullptr){
      ;
    }else {
      coloredInstSet.insert(InstW);
    }
    
    // errs() << "CurrNode: " << *InstW->getInstruction() << "\n";
    DependencyNode<InstructionWrapper>* DNode = PDG->getNodeByData(InstW);
    for(int i = 0; i < DNode->getDependencyList().size(); i++){      
      if(nullptr != DNode->getDependencyList()[i].first->getData()){
	InstructionWrapper *adjacent_InstW = 
	  *InstructionWrapper::nodes.find(const_cast<InstructionWrapper*>(DNode->getDependencyList()[i].first->getData())); 
	/*
	  if(InstW->getInstruction()!= nullptr && adjacent_InstW->getInstruction() != nullptr)
	  errs() << "Curr: " << *InstW->getInstruction() << " --- " << *adjacent_InstW->getInstruction()<<"\n";
	
	  if(InstW->getInstruction()!= nullptr && 
	     isa<ReturnInst>(InstW->getInstruction()) && 
	     adjacent_InstW->getType() == ENTRY)
	  errs() << "Curr: " << *InstW->getInstruction() << " --> " << "ENTRY: " << adjacent_InstW->getFunction()->getName() << "\n";
	  errs() << "DEBUG 1 " << adjacent_InstW->getFlag() << "\n";
	*/
	if(true != adjacent_InstW->getFlag()){

	  // CALL -> ENTRY
	  // CALL Inst -> adjacent_InstW
	  if (InstW->getType() == CALL && adjacent_InstW->getType() == ENTRY){
	    CallInst* CI = dyn_cast<CallInst>(InstW->getInstruction());
	    // must have args
	    int argNum = CI->getNumArgOperands();	     
	    if (argNum > 0){
	      errs() << "Parameter Leak(must have parameters!) : " << InstW->getFunction()->getName() 
		     << " --> " << adjacent_InstW->getFunction()->getName() << "\n\n"; 
	      edgesWithParamLeak.push_back(make_pair(InstW->getFunction()->getName(), adjacent_InstW->getFunction()->getName()));
	    }
	  }
	  if (visitedF.find(adjacent_InstW->getFunction()) == visitedF.end()){
	    errs() << "New Func colored: " << adjacent_InstW->getFunction()->getName() << " ";
	    visitedF.insert(adjacent_InstW->getFunction());
	    //   if(adjacent_InstW->getInstruction() != nullptr)
	    //  errs() << "\nvisitedF: " << visitedF.size() << "\nInst: " << *adjacent_InstW->getInstruction() << "\n";
	    if (InstW->getFunction()->getName() != adjacent_InstW->getFunction()->getName()){
	      if (DNode->getDependencyList()[i].second == RET){
		errs() << "Return Leak : " << InstW->getFunction()->getName() << " ---> " << adjacent_InstW->getFunction()->getName() << "\n";
		edgesWithReturnLeak.push_back(make_pair(adjacent_InstW->getFunction()->getName(), InstW->getFunction()->getName()));
	      }
	    }
	  }
	  //branchInst only generates control dependencies later, so no need to remove branch
	  queue.push_back(DNode->getDependencyList()[i].first->getData());
	  adjacent_InstW->setFlag(true); //label the adjacent node visited
	}
      }
      //      else 
      //	      errs() << "*DNode->getDependencyList()[" << i << "].first->getData = NULL << " << "\n";
    }//end for int i = 0; i < DNode...
    //      errs() << "DEBUG 525" << "\n";
  }//end while(!queue...)

#if 0
  errs() << "\n\n++++++++++SENSITIVE INSTRUCTION List is as follows:++++++++++\n\n";
  int index = 0;
  for(std::set<InstructionWrapper*>::iterator senI = coloredInstSet.begin(); senI != coloredInstSet.end(); ++senI){
    if((*senI)->getType() == INST)
      errs() << "SENSITIVE INSTRUCTION [" << index++ << "] Mem Addr :" << (*senI)->getInstruction() << " Value : " << *(*senI)->getInstruction() << "\n";
  }
#endif
  errs() << "\n\n++++++++++The FUNCTION List is as follows:++++++++++\n\n";
  unsigned int funcs_count = 0;
  unsigned int sen_funcs_count = 0;
  unsigned int ins_funcs_count = 0;
  std::set<FunctionWrapper*> sen_FuncSet;
  std::set<FunctionWrapper*> ins_FuncSet;
  std::map<const llvm::Function *,FunctionWrapper *>::iterator FI =  FunctionWrapper::funcMap.begin();
  std::map<const llvm::Function *,FunctionWrapper *>::iterator FE =  FunctionWrapper::funcMap.end();
  for(; FI != FE; ++FI){
    if(!(*FI).first->isDeclaration()){
      funcs_count++;
      if((*FI).second->hasFuncOrFilePtr()){
	errs() << (*FI).first->getName() << " hasFuncOrFilePtr()\n";
      }
      if((*FI).second->isVisited()){
	//	errs() << (*FI).first->getName() << " is colored(sensitive)\n";
	Function* func = (*FI).second->getFunction();
	//	errs() << "func name = " << func->getName() << "\n";
	sen_FuncSet.insert((*FI).second );
      }
      else{
	//	errs() << (*FI).first->getName() << "is uncolored\n";
	ins_FuncSet.insert((*FI).second );
      }
    }
  }
  errs() << "non-library functions in total: " << funcs_count << "\n";
  errs() << "sen_FuncSet  : " << sen_FuncSet.size() << "\n";
  errs() << "ins_FuncSet  : " << ins_FuncSet.size() << "\n";
  errs() << "functions count = " << funcs <<"\n";

  senFuncs = sen_FuncSet;
  insFuncs = ins_FuncSet;

  /*
    errs() << "=========================== Sensitive Functions List ============================= \n";
    for(auto const &F : senFuncs){
    errs() << F->getFunction()->getName() << "\n";
    }*/

  for (auto &gf : globalTaintedFuncMap){
    errs() << "gf: " << *(gf.first) << " tainted funcs: " << (gf.second).size() << "\n";
    for (auto &F : gf.second){
      errs() << " " << F->getName() << "\n";
    }
  }
  
  ofstream outfile;
  //  outfile.open("./thttpd/global_func_map_thttpd.txt");
    outfile.open("./ssh/global_func_map_ssh.txt");
  //  outfile.open("./wget/global_func_map_wget.txt");
  //  outfile.open("./telnet/global_func_map_telnet.txt");
  if (!outfile.is_open()){
    errs() << "Fail to open global_func_map.txt, file can't be opened!\n ";
    exit(0);
  }
  
  int gvID = 0;
  for(auto &gf : globalTaintedFuncMap){
    //    GlobalValue *gv = dyn_cast<GlobalValue>(gf.first);
    std::string Str;
    raw_string_ostream OS(Str);

    OS << *(gf.first);
    string gv = OS.str();
    unsigned first = gv.find("@");
    unsigned last = gv.find("=") - 1;
    string strnew = gv.substr(first, last-first);
    strnew[0] = '$';

    outfile << gvID++ << " " << strnew << " " << (gf.second).size() << "\n";
    for (auto &F : gf.second)
      outfile << F->getName().str() << "\n";
  }
  outfile.close();

  // print all used global variables(interacted with functions) to a file

#if 0
  ofstream globalout;
  globalout.open("./ssh/global_in_ssh_client.txt");
  //  outfile.open("./thttpd/global_func_map_thttpd.txt");
  //  outfile.open("./ssh/global_func_map_ssh.txt");
  //  outfile.open("./wget/global_func_map_wget.txt");
  //  outfile.open("./telnet/global_func_map_telnet.txt");
  if (!globalout.is_open()){
    errs() << "Fail to open global_in_ssh_client.txt, file can't be opened!\n ";
    exit(0);
  }
  
  for(auto &gf : globalTaintedFuncMap){
    std::string Str;
    raw_string_ostream OS(Str);

    OS << *(gf.first);
    string gv = OS.str();
    unsigned first = gv.find("@");
    unsigned last = gv.find("=") - 1;
    string strnew = gv.substr(first, last-first);
    strnew[0] = '$';

    globalout << strnew << "\n";
  }
  globalout.close();
#endif

  FunctionWrapper::funcMap.clear();
  CallWrapper::callMap.clear();
  InstructionWrapper::nodes.clear();
  InstructionWrapper::globalList.clear();
  InstructionWrapper::instMap.clear();
  InstructionWrapper::funcInstWList.clear();	

  //  allocaMap.clear();
  return false;
}

void ProgramDependencyGraph::getAnalysisUsage(AnalysisUsage &AU) const{
  AU.addRequiredTransitive<AliasAnalysis>();
  AU.addRequired<ControlDependencyGraph>();
  AU.addRequired<DataDependencyGraph>();
  AU.setPreservesAll();
}


void ProgramDependencyGraph::print(llvm::raw_ostream &OS, const llvm::Module*) const{
  PDG->print(OS, getPassName());
}

ProgramDependencyGraph *CreateProgramDependencyGraphPass(){
  return new ProgramDependencyGraph();
}

static RegisterPass<cot::ProgramDependencyGraph> PDG("pdg", "Program Dependency Graph Construction", false, true);
