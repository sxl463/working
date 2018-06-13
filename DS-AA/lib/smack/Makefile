LLVM_CONFIG=llvm-config
CXX=`$(LLVM_CONFIG) --bindir`/clang++
CXXFLAGS=`$(LLVM_CONFIG) --cppflags` -fPIC -fno-rtti -g -O0 -Wno-deprecated -std=c++11
LDFLAGS=`$(LLVM_CONFIG) --ldflags`

all: DSAAliasAnalysis.o

#i_scdg.so: ControlDependencies.o SystemControlDependencies.o DepPrinter.o
#	$(CXX) -shared ControlDependencies.o SystemControlDependencies.o DepPrinter.o -o i_scdg.so $(LDFLAGS) -fPIC

#SystemControlDependencies.o: SystemControlDependenceGraph.cpp SystemControlDependenceGraph.h
#	$(CXX) -c SystemControlDependenceGraph.cpp -o SystemControlDependencies.o $(CXXFLAGS)

#LLVMDataStructure.a: LLVMDataStructure.o
#	$(CXX) -shared *.o -o LLVMDataStructure.a $(LDFLAGS) -fPIC

DSAAliasAnalysis.o:
	$(CXX) -I../../include -c SmackDSAAA.cpp $(CXXFLAGS)

clean:
	rm -f *.o *.a
