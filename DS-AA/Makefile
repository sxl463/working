LLVM_CONFIG=llvm-config
CXX=`$(LLVM_CONFIG) --bindir`/clang++
CXXFLAGS=`$(LLVM_CONFIG) --cppflags` -fPIC -fno-rtti -g -O0 -Wno-deprecated -std=c++11
LDFLAGS=`$(LLVM_CONFIG) --ldflags`

all: ds_aa.so

ds_aa.so:
	$(CXX) -shared lib/AssistDS/DSNodeEquivs.o lib/DSA/LLVMDataStructure.a lib/smack/SmackDSAAA.o lib/sos/DSAA.a -o ds_aa.so $(LDFLAGS) -fPIC
#	$(CXX) -shared DSNodeEquivs.o LLVMDataStructure.a DSAAliasAnalysis.o -o ds_aa.so $(LDFLAGS) -fPIC
#SystemControlDependencies.o: SystemControlDependenceGraph.cpp SystemControlDependenceGraph.h
#	$(CXX) -c SystemControlDependenceGraph.cpp -o SystemControlDependencies.o $(CXXFLAGS)

clean:
	rm -f *.so
