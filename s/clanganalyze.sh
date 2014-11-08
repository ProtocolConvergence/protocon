#!/bin/sh

# Run this from a build directory.
#   cd protocon
#   file CMakeLists.txt
#   mkdir -p bld
#   cd bld
#   ../s/clanganalyze

rm CMakeCache.txt
cmake -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ ..

#export CCC_CC=clang
#export CCC_CXX=clang++
cmake -DCMAKE_C_COMPILER=ccc-analyzer -DCMAKE_CXX_COMPILER=c++-analyzer ..
scan-build -analyze-headers make
#scan-build -analyze-headers --use-analyzer=/usr/bin/clang make

