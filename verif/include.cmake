
enable_testing ()
#include (CTest)

cat_parenthesized (TestNames "${CMAKE_CURRENT_SOURCE_DIR}/testlist.h")

## Unit tests.
foreach (testname ${TestNames})
  add_test (NAME ${testname}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    COMMAND test_exe ${testname})
endforeach ()

cat_parenthesized (DistribSpecs "${CMAKE_CURRENT_SOURCE_DIR}/meta/examplespec.files")
cat_parenthesized (DistribSolns "${CMAKE_CURRENT_SOURCE_DIR}/meta/examplesoln.files")

## Ensure that the specifications that we distribute can be parsed.
foreach (f ${DistribSpecs})
  add_test (NAME ofile_spec_${f}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    COMMAND "${CMAKE_COMMAND}"
    -Dprotocon_exe=$<TARGET_FILE:protocon>
    -Dxfile=examplespec/${f}.protocon
    -P ${CMAKE_CURRENT_SOURCE_DIR}/verif/ofile.cmake
    )
endforeach ()

## Ensure that the solutions that we distribute can be parsed.
foreach (f ${DistribSolns})
  add_test (NAME ofile_soln_${f}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    COMMAND "${CMAKE_COMMAND}"
    -Dprotocon_exe=$<TARGET_FILE:protocon>
    -Dxfile=examplesoln/${f}.protocon
    -P ${CMAKE_CURRENT_SOURCE_DIR}/verif/ofile.cmake
    )
endforeach ()

set (ExampleSpecs
  ColorRing
  ColorTree
  MatchRing
  MatchRingOneBit
  OldOrientRing
  OrientOddRing
  SortChain
  SumNotTarget
  TokenRingSixState
  TokenRingThreeBit
  )

foreach (f ${ExampleSpecs})
  add_test (NAME Synth3_${f}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    COMMAND protocon -x examplespec/${f}.protocon -def N 3)
endforeach ()

foreach (f SortRing TokenRingDijkstra)
  list (APPEND ExampleSpecs ${f})
  add_test (NAME Synth_${f}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    COMMAND protocon -x examplespec/${f}.protocon)
endforeach ()

foreach (f LeaderRingHuang)
  list (APPEND ExampleSpecs ${f})
  add_test (NAME SynthOpenMP_${f}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    COMMAND protocon -parallel 4 -x examplespec/${f}.protocon)
  set_tests_properties (SynthOpenMP_${f} PROPERTIES PROCESSORS 4)

  if (MPI_FOUND)
    add_test (NAME SynthMPI_${f}
      WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
      COMMAND ${MPIEXEC} ${MPIEXEC_NUMPROC_FLAG} 4 ${MPIEXEC_PREFLAGS}
      ${BinPath}/protocon-mpi ${MPIEXEC_POSTFLAGS} -x examplespec/${f}.protocon)
    set_tests_properties (SynthMPI_${f} PROPERTIES PROCESSORS 4)
  endif ()
endforeach ()

list (APPEND ExampleSpecs
  FoundThreeBitTokenRing
  OrientRing
  OrientRingViaToken
  TokenChainDijkstra
  TokenRingSixStateQuiet
  TokenRingThreeState
  )

foreach (f ${ExampleSpecs})
  add_test (NAME Verif5_${f}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    COMMAND protocon -verify -x examplesoln/${f}.protocon -def N 5)
endforeach ()

set (ExampleSynts
  MatchRingOneBit
  ShadowColorRing
  TokenChainDijkstra
  )

foreach (f ${ExampleSynts})
  add_test (NAME TrySynt_${f}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    COMMAND protocon -x examplespec/${f}.protocon -x-try examplesynt/${f}.protocon -def N 5)
  add_test (NAME VerifSynt_${f}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    COMMAND protocon -verify -x examplesynt/${f}.protocon -def N 5)
endforeach ()

add_test (NAME TrySynt2_TokenChainDijkstra
  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
  COMMAND protocon -x examplespec/TokenChainDijkstra.protocon -x-try examplesynt/TokenChainDijkstra.protocon -def N 2)

list (APPEND VerifyBySynthesis
  ColorRing
  FoundThreeBitTokenRing
  OrientRing
  OrientOddRing
  )

foreach (f ${VerifyBySynthesis})
  add_test (NAME VerifSyn_${f}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    COMMAND protocon -x examplesoln/${f}.protocon -def N 5)
endforeach ()

add_test (NAME Verif4_Sync_OrientRing
  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
  COMMAND protocon -verify -synchronous -x examplesoln/OrientRing.protocon -def N 4)

## Ensure our tests can actually detect failure.
add_test (NAME Verif4_OrientOddRing
  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
  COMMAND protocon -verify -x examplesoln/OrientOddRing.protocon -def N 4)
set_tests_properties (Verif4_OrientOddRing PROPERTIES WILL_FAIL TRUE)

