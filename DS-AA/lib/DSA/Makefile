LLVM_CONFIG=llvm-config
CXX=`$(LLVM_CONFIG) --bindir`/clang++
#CXX=g++
CXXFLAGS=`$(LLVM_CONFIG) --cppflags` -fPIC -fno-rtti -g -O0 -Wno-deprecated -std=c++11
#CXXFLAGS=-rdynamic
LDFLAGS=`$(LLVM_CONFIG) --ldflags`# -Wl,--export-dynamic

all: LLVMDataStructure.a

#i_scdg.so: ControlDependencies.o SystemControlDependencies.o DepPrinter.o
#	$(CXX) -shared ControlDependencies.o SystemControlDependencies.o DepPrinter.o -o i_scdg.so $(LDFLAGS) -fPIC

#SystemControlDependencies.o: SystemControlDependenceGraph.cpp SystemControlDependenceGraph.h
#	$(CXX) -c SystemControlDependenceGraph.cpp -o SystemControlDependencies.o $(CXXFLAGS)
LLVMDataStructure.a: LLVMDataStructure.o
	$(CXX) -shared *.o -o LLVMDataStructure.a $(LDFLAGS)

LLVMDataStructure.o:
	$(CXX) -I../../include -c *.cpp $(CXXFLAGS)

clean:
	rm -f *.o *.a
