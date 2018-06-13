#!/bin/bash
file="dsa_mcf_"$(date +"%T")
touch $file
for f in "$1"/*.bc
do
	echo $f
	echo "opt -load ./ds_aa.so -dsa-aa -enable-type-inference-opts -basicaa -aa-eval -disable-output $f" &>> $file
	opt -load ./ds_aa.so -dsa-aa -enable-type-inference-opts -basicaa -aa-eval -disable-output $f &>> $file
done
