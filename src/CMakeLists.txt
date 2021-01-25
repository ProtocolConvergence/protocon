

find_library (M_LIB m)
find_package(MPI)
find_package(OpenMP)

add_definitions(-DPROTOCON_NAMESPACE=protocon)

add_subdirectory(cx)
add_subdirectory(gui)
add_subdirectory(udp-impl)
add_subdirectory(satsyn)


#### Bidirectional Ring Instance Enumeration ####
add_executable(biring
  "biring.cc"
  )
set_property(TARGET biring APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceCxIncludePath}")
target_link_libraries(biring lace_cx_lib)

add_executable(conflictfamily_test
  "conflictfamily_test.cc"
  "conflictfamily.cc"
  "conflictfamily.hh"
  )
set_property(TARGET conflictfamily_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceCxIncludePath}")
target_link_libraries(conflictfamily_test lace_cx_lib)
add_test(NAME conflictfamily_test COMMAND conflictfamily_test)


add_library(pfmla_lib STATIC
  "pfmla.c"
  "pfmla.cc"
  "pfmla-glu.c"
  "pfmla-glu.h"
  "pfmla.h"
  "pfmla.h"
  "pfmla.hh"
  )
set_property(TARGET pfmla_lib
  APPEND PROPERTY INCLUDE_DIRECTORIES ${GluIncludePath})
set_property(TARGET pfmla_lib APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceCxIncludePath}")
target_link_libraries(pfmla_lib lace_cx_lib ${mdd_glu_libs})

add_executable(pfmla_test
  "pfmla_test.cc"
  )
set_property(TARGET pfmla_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceCxIncludePath}")
target_link_libraries(pfmla_test pfmla_lib)
add_test(NAME pfmla_test COMMAND pfmla_test)


add_library(xnsys_lib STATIC
  "xfmlae.cc"
  "xfmlae.hh"
  "xnsys.cc"
  "xnsys.hh"
  "xnpc.cc"
  "xnpc.hh"
  "xnspec.cc"
  "xnspec.hh"
  )
set_property(TARGET xnsys_lib APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceCxIncludePath}")
target_link_libraries(xnsys_lib pfmla_lib)

add_executable(xnsys_test
  "inst.cc"
  "xnsys_test.cc"
  )
set_property(TARGET xnsys_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceCxIncludePath}")
target_link_libraries(xnsys_test xnsys_lib)
add_test(NAME xnsys_test COMMAND xnsys_test)

add_executable(stabilization_test
  "inst.cc"
  "stabilization_test.cc"
  "stabilization.cc"
  "stabilization.hh"
  )
set_property(TARGET stabilization_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceCxIncludePath}")
target_link_libraries(stabilization_test xnsys_lib)
add_test(NAME stabilization_test COMMAND stabilization_test)


#### Parser Generation ####
add_custom_command(
  OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/prot-xfile.leg.cc"
  COMMAND peg_leg -o "${CMAKE_CURRENT_BINARY_DIR}/prot-xfile.leg.cc" "${CMAKE_CURRENT_SOURCE_DIR}/prot-xfile.leg"
  DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/prot-xfile.leg)
set_property(SOURCE "${CMAKE_CURRENT_BINARY_DIR}/prot-xfile.leg.cc"
  APPEND PROPERTY COMPILE_FLAGS "-Wno-unused -Wno-unused-parameter")
set_property(SOURCE "${CMAKE_CURRENT_BINARY_DIR}/prot-xfile.leg.cc"
  APPEND PROPERTY INCLUDE_DIRECTORIES "${CMAKE_CURRENT_SOURCE_DIR}")

add_library(prot_file_lib STATIC
  "pla.cc"
  "pla.hh"
  "prot-ofile.cc"
  "prot-ofile.hh"
  "prot-xfile.cc"
  "prot-xfile.hh"
  "${CMAKE_CURRENT_BINARY_DIR}/prot-xfile.leg.cc"
  "cx/sesp.c"
  "cx/sesp.h"
  )
set_property(TARGET prot_file_lib APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceCxIncludePath}")
target_link_libraries(prot_file_lib xnsys_lib)

#### Deadlock Checking for Generalized Rings ####
add_executable(deadfree
  "deadfree.cc"
  )
set_property(TARGET deadfree APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceCxIncludePath}")
target_link_libraries(deadfree prot_file_lib)

#### Simple Unidirectional Ring Programs ####
add_subdirectory(uni)



set (TopPath ${CMAKE_CURRENT_SOURCE_DIR}/..)
set (BinPath ${TopPath}/bin)
set (DepPath ${TopPath}/dep)

set (CxTopPath ${DepPath}/cx)

#### External Projects ####

ExternalProject_Add(cx_project
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/cx
  SOURCE_DIR ${DepPath}/cx/src
  BINARY_DIR ${DepPath}/cx/bld
  BUILD_ALWAYS 1
  INSTALL_COMMAND echo "No install step."
  )

#### Sources ####

list (APPEND CFiles
  pfmla-bittable.c)

list (APPEND CFiles udp-impl/protocol.c)
list (APPEND HFiles udp-impl/protocol.h udp-impl/act.h)

list (APPEND CCFiles
  opt.cc search.cc
  test.cc
  test-pcxn.cc
  inst.cc main.cc
  main-mpi.cc
  promela.cc graphviz.cc udp-ofile.cc
  interactive.cc
  conflictfamily.cc
  stabilization.cc
  synthesis.cc
  pla.cc
  msat.cc
  )

#### Source-to-Source Tranlation Helpers ####

set (BldPath protocon)
set (TMP_C_FLAGS "${CMAKE_C_FLAGS}")
set (TMP_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
include (${CxTopPath}/src/include.cmake)
set (CMAKE_C_FLAGS "${TMP_C_FLAGS}")
set (CMAKE_CXX_FLAGS "${TMP_CXX_FLAGS}")

add_dependencies (cx cx_project)
add_dependencies (cembed cx_project)
add_dependencies (cswitch cx_project)
add_dependencies (comparispawn cx_project)

set (CMAKE_RUNTIME_OUTPUT_DIRECTORY ${BinPath})



file (MAKE_DIRECTORY ${BldPath}/udp-impl)


#### Common Files ####

list (APPEND ProtoconSources
  pfmla-bittable.c
  pla.cc
  opt.cc inst.cc
  stabilization.cc
  synthesis.cc
  conflictfamily.cc
  )


#### Unit Test Executable ####
addbinexe (test_exe
  test.cc
  test-pcxn.cc
  search.cc
  ${CxBldPath}/kautz.cc
  ${ProtoconSources}
  )
set_property (TARGET test_exe
  APPEND PROPERTY INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})
set_target_properties (test_exe PROPERTIES
  OUTPUT_NAME test
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})
target_link_libraries (test_exe prot_file_lib ${M_LIB})

file (MAKE_DIRECTORY ${BldPath}/test-dep)
add_custom_command (
  OUTPUT ${BldPath}/test-dep/switch.c
  COMMAND cswitch testname
  -case-pfx "fn = Test"
  -array AllTests
  -x ${CMAKE_CURRENT_SOURCE_DIR}/testlist.txt
  -o ${BldPath}/test-dep/switch.c
  DEPENDS cswitch ${CMAKE_CURRENT_SOURCE_DIR}/testlist.txt)
add_custom_target (TestSwitchSources SOURCES ${BldPath}/test-dep/switch.c)

add_dependencies(test_exe TestSwitchSources)


#### Main Executable ####

addbinexe (protocon
  main.cc
  search.cc
  interactive.cc
  promela.cc graphviz.cc udp-ofile.cc
  ${ProtoconSources}
  )
set_property (TARGET protocon
  APPEND PROPERTY INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries (protocon prot_file_lib ${M_LIB})

set (protocon_exe "$<TARGET_FILE:protocon>")

## Set up embedded UDP sources.
# This is an added dependency to the main executable.
set (depfiles)
foreach (depfile udp-impl/protocol.h udp-impl/protocol.c)
  set(ofile ${BldPath}/${depfile}.embed)
  set(xfile ${BldPath}/${depfile})

  add_custom_command (
    OUTPUT ${ofile}
    COMMAND cx -shallow -no-quote-includes -o ${ofile} -x ${xfile}
    DEPENDS ${xfile})
  list (APPEND depfiles ${ofile})
endforeach()

add_custom_command (
  OUTPUT ${BldPath}/udp-impl/act.embed.h
  COMMAND cembed -o ${BldPath}/udp-impl/act.embed.h ${depfiles}
  DEPENDS ${depfiles})
add_custom_target (UdpEmbedSources SOURCES ${BldPath}/udp-impl/act.embed.h)
add_dependencies(protocon UdpEmbedSources)


#### Add OpenMP Flags ####
if (OPENMP_FOUND)
  foreach (target_name protocon test_exe)
    set_property (TARGET ${target_name}
      APPEND_STRING PROPERTY COMPILE_FLAGS " ${OpenMP_C_FLAGS}")
    set_property (TARGET ${target_name}
      APPEND_STRING PROPERTY LINK_FLAGS " ${OpenMP_C_FLAGS}")
  endforeach ()
endif ()


#### Fast Build Rule ####
add_custom_target(some DEPENDS test_exe protocon)


#### Main MPI Executable ####
if (MPI_FOUND)
  addbinexe (protocon-mpi
    main-mpi.cc
    search.cc
    ${CxBldPath}/mpidissem.cc ${CxBldPath}/kautz.cc
    ${ProtoconSources}
    )
  set_property (TARGET protocon-mpi
    APPEND PROPERTY INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR} ${MPI_INCLUDE_PATH})
  target_link_libraries (protocon-mpi ${MPI_LIBRARIES})
  target_link_libraries (protocon-mpi prot_file_lib ${M_LIB})

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


#### MiniSAT Solver Executable ####
# It has problems, not built by default.
set (satccflags "${DEFAULT_COMPILE_FLAGS}")
string (REGEX REPLACE "(^| )[/-]ansi($| )" " "
  satccflags "${satccflags}")
string (REGEX REPLACE "(^| )[/-]pedantic($| )" " "
  satccflags "${satccflags}")

if (FALSE)
  addbinexe (msat msat.cc ${ProtoconSources})
  target_link_libraries (msat minisat prot_file_lib ${M_LIB})
  set_target_properties (msat PROPERTIES
    COMPILE_FLAGS ${satccflags})
  set_property (TARGET msat
    APPEND PROPERTY INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR} "/usr/include/minisat2")
endif()

#### Tests ####
if (EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/verif/include.cmake)
  include (${CMAKE_CURRENT_SOURCE_DIR}/verif/include.cmake)
endif ()


install (TARGETS protocon DESTINATION bin)
if (MPI_FOUND)
  install (TARGETS protocon-mpi DESTINATION bin)
endif()

cat_parenthesized (DistribSpecs ${MetaPath}/examplespec.files)
foreach (f ${DistribSpecs})
  install (FILES ${TopPath}/examplespec/${f}.prot DESTINATION examplespec)
endforeach ()

cat_parenthesized (DistribSetts ${MetaPath}/examplesett.files)
foreach (f ${DistribSetts})
  install (FILES ${TopPath}/examplesett/${f}.args DESTINATION examplesett)
endforeach ()

cat_parenthesized (DistribSynts ${MetaPath}/examplesynt.files)
foreach (f ${DistribSynts})
  install (FILES ${TopPath}/examplesynt/${f}.prot DESTINATION examplesynt)
endforeach ()

cat_parenthesized (DistribSolns ${MetaPath}/examplesoln.files)
foreach (f ${DistribSolns})
  install (FILES ${TopPath}/examplesoln/${f}.prot DESTINATION examplesoln)
endforeach ()

install (FILES ${TopPath}/doc/protocon.1 DESTINATION doc)
install (DIRECTORY ${TopPath}/doc/html/ DESTINATION doc/html)

# Build a CPack-driven installer package.
#   cpack --config CPackConfig.cmake
# Or just:
#   cpack
include (InstallRequiredSystemLibraries)
string (TIMESTAMP CPACK_PACKAGE_VERSION "%Y.%m.%d")
set (CPACK_PACKAGE_VERSION "2015.10.20")
#set (CPACK_GENERATOR "STGZ;TGZ;ZIP")
set (CPACK_GENERATOR "ZIP")
set (MyName "Alex Klinkhamer")
set (CPACK_PACKAGE_VENDOR ${MyName})
set (CPACK_PACKAGE_CONTACT ${MyName})
#set (CPACK_RESOURCE_FILE_LICENSE "${TopPath}/COPYING")
include (CPack)

