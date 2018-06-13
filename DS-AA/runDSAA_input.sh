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
	opt -time-passes -load ./ds_aa.so -smack-ds-aa -disable-dsa-stdlib -enable-type-inference-opts -aa-eval -disable-output $1
fi
