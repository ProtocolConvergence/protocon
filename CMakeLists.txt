
cmake_minimum_required (VERSION 2.8)

project (protocon)

set (CxPath ../cx)
set (BinPath ../bin)
set (BldPath protocon)
set (GluPath ../glu-2.4)
set (GluIncludePath = ${GluPath}/include)

list (APPEND CFiles satsyn.c xnsys.c)
list (APPEND HFiles
  xnsys.h
  dimacs.c pla.c promela.c
  inst-sat3.c inst-matching.c inst-coloring.c
  inst-bit3.c inst-dijkstra.c inst-dijkstra4state.c
  )

list (APPEND CFiles
	pfmla.c pfmla-glu.c pfmla-bittable.c)
list (APPEND HFiles
	pfmla.h pfmla-glu.h pfmla-bittable.h)

list (APPEND CCFiles
	pfmla.cc xnsys.cc test.cc ordersyn.cc main.cc inst.cc promela.cc
	protoconfile.cc)
list (APPEND HHFiles
	pfmla.hh xnsys.hh test.hh ordersyn.hh main.hh inst.hh promela.hh
	protoconfile.hh tuple.hh)

include_directories (${GluIncludePath})
include (${CxPath}/include.cmake)

set (CMAKE_RUNTIME_OUTPUT_DIRECTORY ${BinPath})

addbinexe (satsyn satsyn.c xnsys.c)
#addbinexe (protocon main.cc)

add_custom_command (
  OUTPUT ${BldPathCXX}/protoconfile.leg.cc
  COMMAND leg -o ${BldPathCXX}/protoconfile.leg.cc ${CMAKE_CURRENT_SOURCE_DIR}/protoconfile.leg
  DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/protoconfile.leg)
set_source_files_properties (${BldPathCXX}/protoconfile.leg.cc PROPERTIES GENERATED TRUE)
set_property (SOURCE ${BldPathCXX}/protoconfile.leg.cc
  APPEND PROPERTY OBJECT_DEPENDS ${CxFullHFiles} ${CxFullHHFiles} ${FullHFiles} ${FullHHFiles})

link_directories(${GluPath})
addbinexe (protocon
  pfmla.cc xnsys.cc test.cc ordersyn.cc main.cc inst.cc promela.cc protoconfile.cc protoconfile.leg.cc
  pfmla.c pfmla-glu.c pfmla-bittable.c
  )
target_link_libraries (protocon cu glu cal m)

#target_link_libraries (chatty rt)

