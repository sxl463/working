//
#include "llvm/Bitcode/ReaderWriter.h"

#include "FunctionWrapper.h"

#include "ProgramDependencies.h"
#include "SystemDataDependencies.h"
#include "SystemControlDependenceGraph.h"

#include "AllPasses.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/DerivedTypes.h"

#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"
#include <map>
#include <vector>
#include <iostream>

using namespace std;
using namespace cot;
using namespace llvm;

void ConnectFunctions(){
  errs() << "connect_caller_callee!" << "\n";
}
