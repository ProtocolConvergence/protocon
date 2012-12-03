
cmake_minimum_required (VERSION 2.8)

project (satsyn)

set (CxPath ../cx)
set (BinPath ../bin)
set (BldPath satsyn)

list (APPEND CFiles satsyn.c xnsys.c)
list (APPEND HFiles
	xnsys.h
    dimacs.c pla.c promela.c
    inst-sat3.c inst-matching.c inst-coloring.c
    inst-bit3.c inst-dijkstra.c inst-dijkstra4state.c
    )

include (${CxPath}/include.cmake)


set (CMAKE_RUNTIME_OUTPUT_DIRECTORY ${BinPath})

addbinexe (satsyn xnsys.c)


