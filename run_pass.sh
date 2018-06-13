#!/bin/sh

#CXX=/usr/llvm-3.3/bin/clang
#OPT=/usr/llvm-3.3/bin/opt
CXX=/usr/local/bin/clang
OPT=/usr/local/bin/opt

#CXX=`$(CLANG_CONFIG)`/clang
#CXXFLAGS=``

if [ "$1" != "" ]; then
    echo "file parameter:" $1
#	llvm-dis < $1



#	$OPT -load ./pdg.so -cdg  < $1 > /dev/null
#	$OPT -basicaa -load ./pdg.so -ddg  < $1 > /dev/null    

#	$OPT -basicaa -load ./pdg.so -ddg  < $1 > /dev/null	

#	$OPT -basicaa -load ./pdg.so -pdg  < $1 > /dev/null    

#	$OPT -basicaa -load ./pdg.so -scdg  < $1 > /dev/null    
#	$OPT -basicaa -load ./pdg.so -sdg  < $1 > /dev/null    

#	$OPT -load ./pdg.so -pdg  < $1 > /dev/null


# generate dot files
#	$OPT -basicaa -load ./pdg.so -dot-cdg < $1 > /dev/null

#	$OPT -time-passes -basicaa -load ./pdg.so -dot-ddg < $1 > /dev/null

#	$OPT -load  ./pdg.so -basicaa -dot-pdg -time-passes < $1 > /dev/null


#	$OPT -load ./pdg.so -smack-ds-aa -pdg -dot-pdg -debug-pass=Structure -time-passes < $1 > /dev/null


#	$OPT -load ./pdg.so -smack-ds-aa -pdg -get-call-graph -dot-pdg -debug-pass=Structure -time-passes < $1 > /dev/null

	$OPT -load ./pdg.so -smack-ds-aa -get-call-graph -debug-pass=Structure -time-passes < $1 > /dev/null


	mv *.dot ./visualization

#	$OPT -load  ./pdg.so -basicaa -dot-pdg -debug-pass=Structure -time-passes < $1 > /dev/null
#	$OPT -load ./pdg.so -dot-sdg < $1 > /dev/null
#	$OPT -load ./pdg.so -dot-scdg < $1 > /dev/null
#	$OPT -basicaa -load ./pdg.so -dot-pdg < $1 > /dev/null

#	./dot2png.sh
    
else
    echo "File input is requried!"
fi


#$CXX  -emit-llvm -c test.c -o test.bc







#dot -Tpng -o cdg.png cdgragh.test.dot
#dot -Tpng -o ddg.png ddgragh.test.dot
#dot -Tpng -o pdg.png pdgragh.test.dot
echo "building program dependency graph..."
echo "Done, please enter /visualization and view"

dot -Tsvg -o ./visualization/pdg.svg ./visualization/pdgragh.main.dot

#$OPT -load ./pdg.so -view-cdg < test.bc > /dev/null

#/usr/llvm-3.3/bin/opt -load ./pdg.so -view-cdg < test.bc > /dev/null
