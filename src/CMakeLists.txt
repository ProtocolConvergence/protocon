
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
  "${LaceIncludeDir}")
target_link_libraries(biring cx_lib)

add_executable(conflictfamily_test
  "conflictfamily_test.cc"
  "conflictfamily.cc"
  "conflictfamily.hh"
  )
set_property(TARGET conflictfamily_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries(conflictfamily_test cx_lib)
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
  "${LaceIncludeDir}")
target_link_libraries(pfmla_lib cx_lib ${mdd_glu_libs})

add_executable(pfmla_test
  "pfmla_test.cc"
  )
set_property(TARGET pfmla_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
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
  "${LaceIncludeDir}")
target_link_libraries(xnsys_lib pfmla_lib)

add_executable(xnsys_test
  "inst.cc"
  "xnsys_test.cc"
  )
set_property(TARGET xnsys_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries(xnsys_test xnsys_lib)
add_test(NAME xnsys_test COMMAND xnsys_test)

add_executable(stabilization_test
  "inst.cc"
  "stabilization_test.cc"
  "stabilization.cc"
  "stabilization.hh"
  )
set_property(TARGET stabilization_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries(stabilization_test xnsys_lib)
add_test(NAME stabilization_test COMMAND stabilization_test)


#### Parser Generation ####
add_custom_command(
  OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/prot-xfile.leg.cc"
  COMMAND peg_leg -o "${CMAKE_CURRENT_BINARY_DIR}/prot-xfile.leg.cc" "${CMAKE_CURRENT_SOURCE_DIR}/prot-xfile.leg"
  DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/prot-xfile.leg)

add_library(prot_file_lib STATIC
  "lace_wrapped.hh"
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
  "${LaceIncludeDir}" "${CMAKE_CURRENT_SOURCE_DIR}")
target_link_libraries(prot_file_lib xnsys_lib)

#### Deadlock Checking for Generalized Rings ####
add_executable(deadfree
  "deadfree.cc"
  )
set_property(TARGET deadfree APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries(deadfree prot_file_lib)

#### Simple Unidirectional Ring Programs ####
add_subdirectory(uni)


## Set up embedded UDP sources.
# This is an added dependency to the main executable.
add_custom_command(
  OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/udp-impl/act.embed.h"
  COMMAND cembed -o "${CMAKE_CURRENT_BINARY_DIR}/udp-impl/act.embed.h" "${CMAKE_CURRENT_SOURCE_DIR}/udp-impl/protocol.h" "${CMAKE_CURRENT_SOURCE_DIR}/udp-impl/protocol.c"
  DEPENDS "udp-impl/protocol.h" "udp-impl/protocol.c")

#### Main Executable Lib without Search ####
add_library(protocon_lib STATIC
  "conflictfamily.cc"
  "conflictfamily.hh"
  "graphviz.cc"
  "graphviz.hh"
  "inst.cc"
  "inst.hh"
  "interactive.cc"
  "interactive.hh"
  "opt.cc"
  "opt.hh"
  "pfmla-bittable.c"
  "pfmla-bittable.h"
  "promela.cc"
  "promela.hh"
  "stabilization.cc"
  "stabilization.hh"
  "synthesis.cc"
  "synthesis.hh"
  "udp-ofile.cc"
  "udp-ofile.hh"
  "${CMAKE_CURRENT_BINARY_DIR}/udp-impl/act.embed.h"
  )
set_property(TARGET protocon_lib APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}" "${CMAKE_CURRENT_BINARY_DIR}")
target_link_libraries(protocon_lib prot_file_lib)


## Code for unit test executable.
add_custom_command (
  OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/test.embed.h"
  COMMAND cswitch testname
  -case-pfx "fn = Test"
  -array AllTests
  -x "${CMAKE_CURRENT_SOURCE_DIR}/testlist.txt"
  -o "${CMAKE_CURRENT_BINARY_DIR}/test.embed.h"
  DEPENDS "testlist.txt")

#### Unit Test Executable ####
add_executable(test_exe
  "kautz.cc"
  "kautz.hh"
  "search.cc"
  "search.hh"
  "test.cc"
  "test-pcxn.cc"
  "${CMAKE_CURRENT_BINARY_DIR}/test.embed.h"
  )
set_property(TARGET test_exe APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}" "${CMAKE_CURRENT_BINARY_DIR}")
target_link_libraries (test_exe protocon_lib ${M_LIB})


#### Main Executable ####
add_executable(protocon
  "main.cc"
  "main-all.hh"
  "search.cc"
  "search.hh"
  )
set_property(TARGET protocon APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries (protocon protocon_lib ${M_LIB})

set_target_properties(protocon PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/..")

set (protocon_exe "$<TARGET_FILE:protocon>")

#### Add OpenMP Flags ####
if (OPENMP_FOUND)
  foreach (target_name protocon test_exe)
    set_property (TARGET ${target_name}
      APPEND_STRING PROPERTY COMPILE_FLAGS " ${OpenMP_C_FLAGS}")
    set_property (TARGET ${target_name}
      APPEND_STRING PROPERTY LINK_FLAGS " ${OpenMP_C_FLAGS}")
  endforeach ()
endif ()


#### Main MPI Executable ####
if (MPI_FOUND)
  add_executable(protocon-mpi
    "kautz.cc"
    "kautz.hh"
    "main-all.hh"
    "main-mpi.cc"
    "mpidissem.cc"
    "mpidissem.hh"
    "search.cc"
    "search.hh"
    )
  set_property (TARGET protocon-mpi APPEND PROPERTY INCLUDE_DIRECTORIES
    "${LaceIncludeDir}" "${MPI_INCLUDE_PATH}")
  target_link_libraries (protocon-mpi ${MPI_LIBRARIES})
  target_link_libraries (protocon-mpi protocon_lib ${M_LIB})

  if(MPI_COMPILE_FLAGS)
    set (MPI_COMPILE_FLAGS "${MPI_COMPILE_FLAGS} ${DEFAULT_COMPILE_FLAGS}")
  else()
    set (MPI_COMPILE_FLAGS "${DEFAULT_COMPILE_FLAGS}")
  endif()

  set_target_properties (protocon-mpi PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/.."
    COMPILE_FLAGS "${MPI_COMPILE_FLAGS}")

  if(MPI_LINK_FLAGS)
    set_target_properties (protocon-mpi PROPERTIES
      LINK_FLAGS "${MPI_LINK_FLAGS}")
  endif()
endif()


#### MiniSAT Solver Executable ####
# It has problems, not built by default.
if (FALSE)
  add_executable (msat "msat.cc")
  target_link_libraries (msat minisat protocon_lib ${M_LIB})
  set_property (TARGET msat APPEND PROPERTY INCLUDE_DIRECTORIES
    "${LaceIncludeDir}" "/usr/include/minisat2")
endif()


# Call with
#   cat_parenthesized (mylist, filename)
# to set `mylist` to contain the content between parentheses
# on lines in the given file.
function (cat_parenthesized dst f)
  file(READ ${f} tmp)
  string(REPLACE "\n" ";" tmp "${tmp}")
  string(REGEX REPLACE "[^;\\(]*\\( *([^\\) ]*) *\\) *" "\\1" tmp "${tmp}")
  set(${dst} ${tmp} PARENT_SCOPE)
endfunction ()


#### Tests ####
set (TopPath ${CMAKE_CURRENT_SOURCE_DIR}/..)
include (${CMAKE_CURRENT_SOURCE_DIR}/verif/include.cmake)


#### Install ####

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

