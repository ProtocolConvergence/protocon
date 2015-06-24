
cmake_minimum_required (VERSION 2.8)
set(CMAKE_DISABLE_SOURCE_CHANGES ON)
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)

project (protocon)

#SET(CMAKE_CXX_FLAGS_DEBUG "-g3")
#SET(CMAKE_C_FLAGS_DEBUG "-g3")
#set (CMAKE_BUILD_TYPE DEBUG)
#set (CMAKE_BUILD_TYPE RELEASE)
#set (CMAKE_BUILD_TYPE RelWithDebInfo)

find_library (M_LIB m)
find_package(MPI)
find_package(OpenMP)

set (TopPath ${CMAKE_CURRENT_SOURCE_DIR}/..)
set (DepPath ${TopPath}/dep)
set (CxTopPath ${DepPath}/cx)
set (CxPath ${CxTopPath}/src)
set (CxBinPath ${CxTopPath}/bin)
set (BinPath ${CMAKE_CURRENT_SOURCE_DIR}/../bin)
if (NOT DEFINED GluPath)
  set (GluPath ${DepPath}/glu-2.4)
endif ()
set (BldPath protocon)
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
list (APPEND HFiles udp.h udp-act.h testlist.h)

list (APPEND CCFiles
  pfmla.cc xfmlae.cc xnsys.cc xnspec.cc
  opt.cc search.cc
  test.cc inst.cc main.cc
  main-mpi.cc
  promela.cc graphviz.cc udp-ofile.cc
  interactive.cc
  conflictfamily.cc
  stabilization.cc
  synthesis.cc
  prot-xfile.cc prot-ofile.cc
  biring.cc
  deadfree.cc
  msat.cc
  )
list (APPEND HHFiles
  pfmla.hh xfmlae.hh xnsys.hh xnspec.hh
  opt.hh search.hh
  inst.hh
  promela.hh graphviz.hh udp-ofile.hh
  interactive.hh
  conflictfamily.hh
  stabilization.hh
  synthesis.hh
  prot-xfile.hh prot-ofile.hh
  tuple.hh
  )

include (${CxPath}/include.cmake)

set (CMAKE_RUNTIME_OUTPUT_DIRECTORY ${BinPath})

add_subdirectory (gui)

addbinexe (satsyn satsyn/satsyn.c satsyn/xnsys.c)

file (MAKE_DIRECTORY ${BldPath}/satsyn)
file (MAKE_DIRECTORY ${BldPath}/udp-dep)

if (NOT DEFINED PegExe)
  set (PegExe leg)
endif ()

if (NOT DEFINED CEmbedExe)
  set (CEmbedExe ${CxBinPath}/cembed)
endif ()

add_custom_command (
  OUTPUT ${BldPath}/prot-xfile.leg.cc
  COMMAND ${PegExe} -o ${BldPath}/prot-xfile.leg.cc ${CMAKE_CURRENT_SOURCE_DIR}/prot-xfile.leg
  DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/prot-xfile.leg)
set_bld_cfile_properties (${BldPath}/prot-xfile.leg.cc)

#### Set up embedded UDP sources. ####
set (depfiles)
foreach (depfile cx/def.h cx/synhax.h udp.h udp.c)
  pfxeq (in_cx cx/ ${depfile})
  string(REGEX REPLACE "^.*/" "" depfile "${depfile}")
  set(ofile ${BldPath}/udp-dep/${depfile})

  if (in_cx)
    set(xfile ${CxBldPath}/${depfile})
  else ()
    set(xfile ${BldPath}/${depfile})
  endif ()

  add_custom_command (
    OUTPUT ${ofile}
    COMMAND ${CxExe} -shallow -no-quote-includes -o ${ofile} -x ${xfile}
    DEPENDS ${xfile})
  list (APPEND depfiles ${ofile})
endforeach()

add_custom_command (
  OUTPUT ${BldPath}/udp-dep/embed.h
  COMMAND ${CEmbedExe} -o ${BldPath}/udp-dep/embed.h ${depfiles}
  DEPENDS ${depfiles})
add_custom_target (UdpEmbedSources SOURCES ${BldPath}/udp-dep/embed.h)
#### Done setting up embedded UDP sources ####

list (APPEND ProtoconSources
  pfmla.c pfmla.cc xfmlae.cc
  pfmla-glu.c pfmla-bittable.c
  xnspec.cc xnsys.cc
  prot-xfile.cc prot-xfile.leg.cc prot-ofile.cc
  opt.cc inst.cc
  stabilization.cc
  synthesis.cc
  conflictfamily.cc
  )

link_directories(${GluPath})

addbinexe (test_exe
  test.cc
  search.cc
  ${CxBldPath}/kautz.cc
  ${ProtoconSources}
  )
set_target_properties (test_exe PROPERTIES
  OUTPUT_NAME test
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
set_property (TARGET test_exe
  APPEND PROPERTY INCLUDE_DIRECTORIES ${GluIncludePath})
target_link_libraries (test_exe cu glu cal ${M_LIB})

addbinexe (protocon
  main.cc
  search.cc
  interactive.cc
  promela.cc graphviz.cc udp-ofile.cc
  ${ProtoconSources}
  )
add_dependencies(protocon UdpEmbedSources)
set_property (TARGET protocon
  APPEND PROPERTY INCLUDE_DIRECTORIES ${GluIncludePath})
target_link_libraries (protocon cu glu cal ${M_LIB})

addbinexe (biring biring.cc)
set_target_properties (biring PROPERTIES
  OUTPUT_NAME biring
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})

addbinexe (deadfree deadfree.cc ${ProtoconSources})
set_property (TARGET deadfree
  APPEND PROPERTY INCLUDE_DIRECTORIES ${GluIncludePath})
target_link_libraries (deadfree cu glu cal ${M_LIB})
set_target_properties (deadfree PROPERTIES
  OUTPUT_NAME deadfree
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})

if (UNIX)
  addbinexe (udp udp.c)
  target_link_libraries (udp rt)
  set_property (TARGET udp
    APPEND PROPERTY COMPILE_DEFINITIONS _POSIX_C_SOURCE=199309L)
  set_property (TARGET udp
    APPEND PROPERTY COMPILE_DEFINITIONS _BSD_SOURCE)

  set_target_properties (udp PROPERTIES
    OUTPUT_NAME udp
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
endif ()


if (MPI_FOUND)
  addbinexe (protocon-mpi
    main-mpi.cc
    search.cc
    ${CxBldPath}/mpidissem.cc ${CxBldPath}/kautz.cc
    ${ProtoconSources}
    )
  set_property (TARGET protocon-mpi
    APPEND PROPERTY INCLUDE_DIRECTORIES ${GluIncludePath} ${MPI_INCLUDE_PATH})
  target_link_libraries (protocon-mpi ${MPI_LIBRARIES})
  target_link_libraries (protocon-mpi cu glu cal ${M_LIB})

  if(MPI_COMPILE_FLAGS)
    set (MPI_COMPILE_FLAGS "${MPI_COMPILE_FLAGS} ${DEFAULT_COMPILE_FLAGS}")
  else()
    set (MPI_COMPILE_FLAGS ${DEFAULT_COMPILE_FLAGS})
  endif()

  string (REGEX REPLACE "(^| )[/-]ansi($| )" " "
    MPI_COMPILE_FLAGS "${MPI_COMPILE_FLAGS}")
  string (REGEX REPLACE "(^| )[/-]pedantic($| )" " "
    MPI_COMPILE_FLAGS "${MPI_COMPILE_FLAGS}")

  set_target_properties (protocon-mpi PROPERTIES
    COMPILE_FLAGS ${MPI_COMPILE_FLAGS})

  if(MPI_LINK_FLAGS)
    set_target_properties (protocon-mpi PROPERTIES
      LINK_FLAGS "${MPI_LINK_FLAGS}")
  endif()
endif ()

if (OPENMP_FOUND)
  foreach (target_name protocon test_exe)
    set_property (TARGET ${target_name}
      APPEND_STRING PROPERTY COMPILE_FLAGS " ${OpenMP_C_FLAGS}")
    set_property (TARGET ${target_name}
      APPEND_STRING PROPERTY LINK_FLAGS " ${OpenMP_C_FLAGS}")
  endforeach ()
endif ()



set (satccflags "${DEFAULT_COMPILE_FLAGS}")
string (REGEX REPLACE "(^| )[/-]ansi($| )" " "
  satccflags "${satccflags}")
string (REGEX REPLACE "(^| )[/-]pedantic($| )" " "
  satccflags "${satccflags}")

if (FALSE)
  addbinexe (msat msat.cc ${ProtoconSources})
  target_link_libraries (msat minisat cu glu cal ${M_LIB})
  set_target_properties (msat PROPERTIES
    COMPILE_FLAGS ${satccflags})
  set_property (TARGET msat
    APPEND PROPERTY INCLUDE_DIRECTORIES ${GluIncludePath})
  set_property (TARGET msat
    APPEND PROPERTY INCLUDE_DIRECTORIES "/usr/include/minisat2")
endif()


if (EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/verif/include.cmake)
  include (${CMAKE_CURRENT_SOURCE_DIR}/verif/include.cmake)
endif ()

