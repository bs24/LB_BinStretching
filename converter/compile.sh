#!/bin/bash

usage()
{
	echo "usage: ./compile.sh m t g"
	echo "where m: number of bins/machines (e.g. 6)"
	echo "      t: target load (e.g. 19)"
	echo "      g: load of the optimum (e.g. 14)"
}

if [ $# -ne 3 ]; then
	usage
	exit 1
fi

if [ ! -d  build/ ]; then
	mkdir build
fi

echo "Compiling converter binary for $1 bins and ratio $2/$3 into converter/build/rooster-$1-$2-$3."
cd build; g++ -I../ -Wall -std=c++17 -O3 -march=native -DIBINS=$1 -DIR=$2 -DIS=$3 -DII_S="{}" ../rooster.cpp -o ./rooster-$1-$2-$3 -pthread; cd ..
