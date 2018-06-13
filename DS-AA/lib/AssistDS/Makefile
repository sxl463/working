##===- lib/AssistDS/Makefile -------------------------------*- Makefile -*-===##
# 
#                     The LLVM Compiler Infrastructure
#
# This file was developed by the LLVM research group and is distributed under
# the University of Illinois Open Source License. See LICENSE.TXT for details.
# 
##===----------------------------------------------------------------------===##
# old Makefile using LLVM style
#LEVEL = ../..
#LIBRARYNAME = AssistDS
#BUILD_ARCHIVE=1

#include $(LEVEL)/Makefile.common

#CFlags += -Wno-deprecated



LLVM_CONFIG=llvm-config
CXX=`$(LLVM_CONFIG) --bindir`/clang++
CXXFLAGS=`$(LLVM_CONFIG) --cppflags` -fPIC -fno-rtti -g -O0 -Wno-deprecated -std=c++11
LDFLAGS=`$(LLVM_CONFIG) --ldflags`

all: DSNodeEquivs.o

#i_scdg.so: ControlDependencies.o SystemControlDependencies.o DepPrinter.o
#	$(CXX) -shared ControlDependencies.o SystemControlDependencies.o DepPrinter.o -o i_scdg.so $(LDFLAGS) -fPIC

#SystemControlDependencies.o: SystemControlDependenceGraph.cpp SystemControlDependenceGraph.h
#	$(CXX) -c SystemControlDependenceGraph.cpp -o SystemControlDependencies.o $(CXXFLAGS)

#LLVMDataStructure.a: LLVMDataStructure.o
#	$(CXX) -shared *.o -o LLVMDataStructure.a $(LDFLAGS) -fPIC

DSNodeEquivs.o:
	$(CXX) -I../../include -c DSNodeEquivs.cpp $(CXXFLAGS)

clean:
	rm -f *.o *.a
