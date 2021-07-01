#!/bin/sh

DIR="spacer-benchmarks"

for dir in $DIR
do 
	SUBDIR_LIST=`find ./$dir -name *.smt2`
	for sub in $SUBDIR_LIST
	do
		echo $sub
		python src/main.py $sub
	done
done
	
