
cmake_minimum_required (VERSION 2.8)

set(CMAKE_DISABLE_SOURCE_CHANGES ON)
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)

project (protocon)

#set (CMAKE_BUILD_TYPE RELEASE)
#set (CMAKE_BUILD_TYPE RelWithDebInfo)

find_package(MPI)
find_package(OpenMP)

set (CxPath ${CMAKE_CURRENT_SOURCE_DIR}/../cx)
set (BinPath ${CMAKE_CURRENT_SOURCE_DIR}/../bin)
set (BldPath protocon)
set (GluPath ${CMAKE_CURRENT_SOURCE_DIR}/../glu-2.4)
set (GluIncludePath ${GluPath}/include)

list (APPEND CFiles satsyn/satsyn.c satsyn/xnsys.c)
list (APPEND HFiles
  satsyn/xnsys.h
  satsyn/dimacs.c satsyn/pla.c satsyn/promela.c
  satsyn/inst-sat3.c satsyn/inst-matching.c satsyn/inst-coloring.c
  satsyn/inst-bit3.c satsyn/inst-dijkstra.c satsyn/inst-dijkstra4state.c
  )

list (APPEND CFiles
  pfmla.c pfmla-glu.c pfmla-bittable.c)
list (APPEND HFiles
  pfmla.h pfmla-glu.h pfmla-bittable.h)

list (APPEND CFiles udp.c)
list (APPEND HFiles udp-act.h)

list (APPEND CCFiles
  pfmla.cc xnsys.cc xnspec.cc
  opt.cc search.cc
  test.cc inst.cc main.cc
  main-mpi.cc mpidissem.cc
  promela.cc pla.cc graphviz.cc kautz.cc
  interactive.cc
  conflictfamily.cc
  stabilization.cc
  synthesis.cc
  protoconfile.cc
  biring.cc
  deadfree.cc
  )
list (APPEND HHFiles
  pfmla.hh xnsys.hh xnspec.hh
  opt.hh search.hh
  test.hh inst.hh
  mpidissem.hh
  promela.hh pla.hh graphviz.hh kautz.hh
  interactive.hh
  conflictfamily.hh
  stabilization.hh
  synthesis.hh
  protoconfile.hh tuple.hh
  )

include_directories (${GluIncludePath})
include (${CxPath}/include.cmake)

set (CMAKE_RUNTIME_OUTPUT_DIRECTORY ${BinPath})

add_subdirectory (gui)

addbinexe (satsyn satsyn/satsyn.c satsyn/xnsys.c)

file (MAKE_DIRECTORY ${BldPath}/satsyn)

if (NOT DEFINED PegExe)
  set (PegExe leg)
endif ()

add_custom_command (
  OUTPUT ${BldPath}/protoconfile.leg.cc
  COMMAND ${PegExe} -o ${BldPath}/protoconfile.leg.cc ${CMAKE_CURRENT_SOURCE_DIR}/protoconfile.leg
  DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/protoconfile.leg)
set_source_files_properties (${BldPath}/protoconfile.leg.cc PROPERTIES GENERATED TRUE)
set_property (SOURCE ${BldPath}/protoconfile.leg.cc
  APPEND PROPERTY OBJECT_DEPENDS ${CxFullHFiles} ${CxFullHHFiles} ${FullHFiles} ${FullHHFiles})

list (APPEND ProtoconSources
  pfmla.cc xnsys.cc inst.cc
  opt.cc search.cc
  promela.cc pla.cc graphviz.cc kautz.cc
  stabilization.cc
  synthesis.cc
  interactive.cc
  conflictfamily.cc
  protoconfile.cc protoconfile.leg.cc
  pfmla.c pfmla-glu.c pfmla-bittable.c
  )

link_directories(${GluPath})

addbinexe (test test.cc ${ProtoconSources})
set_target_properties (test PROPERTIES
  OUTPUT_NAME test
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries (test cu glu cal m)

addbinexe (protocon
  ${ProtoconSources}
  main.cc
  )
if (OPENMP_FOUND)
  set_property (TARGET protocon
    APPEND PROPERTY COMPILE_FLAGS ${OpenMP_C_FLAGS})
  set_property (TARGET protocon
    APPEND PROPERTY LINK_FLAGS ${OpenMP_C_FLAGS})
endif ()
target_link_libraries (protocon cu glu cal m)

addbinexe (biring biring.cc)
set_target_properties (biring PROPERTIES
  OUTPUT_NAME biring
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})

addbinexe (deadfree ${ProtoconSources} deadfree.cc)
target_link_libraries (deadfree cu glu cal m)
set_target_properties (deadfree PROPERTIES
  OUTPUT_NAME deadfree
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})

addbinexe (udp udp.c)
target_link_libraries (udp rt)
set_property (TARGET udp
  APPEND PROPERTY COMPILE_DEFINITIONS _POSIX_C_SOURCE=199309L)
set_property (TARGET udp
  APPEND PROPERTY COMPILE_DEFINITIONS _BSD_SOURCE)

set_target_properties (udp PROPERTIES
  OUTPUT_NAME udp
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})

#target_link_libraries (chatty rt)

if (MPI_FOUND)
  include_directories(${MPI_INCLUDE_PATH})
  addbinexe (protocon-mpi
    ${ProtoconSources}
    main-mpi.cc mpidissem.cc
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
endif ()

