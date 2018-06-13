LLVM_CONFIG=llvm-config
CXX=`$(LLVM_CONFIG) --bindir`/clang++
CXXFLAGS=`$(LLVM_CONFIG) --cppflags` -fPIC -fno-rtti -g -O0 -Wno-deprecated -std=c++11
LDFLAGS=`$(LLVM_CONFIG) --ldflags`

all: DSAA.a

DSAA.a: DSAA.o
	$(CXX) -shared *.o -o DSAA.a $(LDFLAGS) -fPIC

DSAA.o:
	$(CXX) -I../../include -c AliasAnalysisEvaluator.cpp DSA_AA.cpp $(CXXFLAGS)

clean:
	rm -f *.o *.a
