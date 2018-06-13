#!/bin/bash
#file="dsa_mcf_"$(date +"%T")
#touch $file
#for f in /home/zhiyuan/codeblocks/benchmark/429.mcf/src/*.bc
#do
#	echo $f
#	echo "opt -load ./ds_aa.so -dsa-aa -aa-eval -disable-output $f"
#	opt -load ./ds_aa.so -dsa-aa -aa-eval -disable-output $f
#done
echo $1
if [ "$1" != "" ]; then
	opt -load ./ds_aa.so -dsa-aa -aa-eval -disable-output -print-may-aliases -print-no-aliases -print-must-aliases $1 --debug
fi
