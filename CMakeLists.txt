
cmake_minimum_required (VERSION 2.8)

project (protocon)

set (CxPath ../cx)
set (BinPath ../bin)
set (BldPath protocon)
set (GluPath ../glu-2.4)
set (GluIncludePath ${GluPath}/include)

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
	pfmla.cc xnsys.cc test.cc main.cc inst.cc
  opt.cc search.cc
  main-mpi.cc
  promela.cc pla.cc
  conflictfamily.cc
  stabilization.cc
  synthesis.cc
	protoconfile.cc
  )
list (APPEND HHFiles
	pfmla.hh xnsys.hh test.hh main.hh inst.hh
  opt.hh search.hh
  promela.hh pla.hh
  conflictfamily.hh
  stabilization.hh
  synthesis.hh
	protoconfile.hh tuple.hh
  )

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

list (APPEND ProtoconSources
  pfmla.cc xnsys.cc inst.cc
  opt.cc search.cc
  promela.cc pla.cc
  stabilization.cc
  synthesis.cc
  conflictfamily.cc
  protoconfile.cc protoconfile.leg.cc
  pfmla.c pfmla-glu.c pfmla-bittable.c
  )

link_directories(${GluPath})
addbinexe (protocon
  ${ProtoconSources}
  test.cc main.cc
  )
target_link_libraries (protocon cu glu cal m)

find_package(MPI REQUIRED)
include_directories(${MPI_INCLUDE_PATH})
addbinexe (protocon-mpi
  ${ProtoconSources}
  main-mpi.cc
  )
target_link_libraries (protocon-mpi ${MPI_LIBRARIES})
target_link_libraries (protocon-mpi cu glu cal m)

if(MPI_COMPILE_FLAGS)
  set_target_properties (protocon-mpi PROPERTIES
    COMPILE_FLAGS "${MPI_COMPILE_FLAGS}")
endif()

if(MPI_LINK_FLAGS)
  set_target_properties (protocon-mpi PROPERTIES
    LINK_FLAGS "${MPI_LINK_FLAGS}")
endif()


#target_link_libraries (chatty rt)

