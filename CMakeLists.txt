
cmake_minimum_required (VERSION 2.8)

project (satsyn)

set (CxPath ../cx)
set (BinPath ../bin)
set (BldPath satsyn)

list (APPEND CFiles satsyn.c)
list (APPEND HFiles
    dimacs.c pla.c promela.c
    inst-sat3.c inst-matching.c inst-coloring.c inst-bit3.c inst-dijkstra.c
    )

include (${CxPath}/include.cmake)


set (CMAKE_RUNTIME_OUTPUT_DIRECTORY ${BinPath})

addbinexe (satsyn)


