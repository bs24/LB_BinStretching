#!/bin/bash

# usage: bash testnewtree.sh t g m
# the input file must be present (file.v) or compressed (file.v.xz) in witnesses/

if [ "$#" -ne 3 ]; then
    echo "Error: Expected 3 arguments: m t g" 
    echo "where m: number of bins/machines (e.g. 6)"
    echo "      t: target load (e.g. 19)"
    echo "      g: load of the optimum (e.g. 14)"
    exit
fi

file="lb_$1_$2_$3"

if [ ! -f "witnesses/$file.v" ]; then
	if [ ! -f "witnesses/$file.v.xz" ]; then
	    echo "Error: witnesses/$file.v and witnesses/$file.v.xz do not exist"
	    exit
	else
	    echo "decompressing witnesses/$file.v.xz"
	    xz -kd "witnesses/$file.v.xz"
	fi
fi

echo "-R . Top
./binstretching.v
./coq_gen_script.v
witnesses/$file.v" > _GenCoqProject

echo " (* automatically generated *)
Require Import binstretching.
Require Import $file. 

Theorem NewLB: Lower_bound $1 $2 $3.
Proof.
Time apply Lower_bound_recordN; auto with arith; exists $file.lb_T ; exists $file.lb_R; vm_compute; eauto.
Time Qed.
Check NewLB.
Print Assumptions NewLB.



" > coq_gen_script.v

coq_makefile -f  _GenCoqProject -o Makefile && time (make) 

