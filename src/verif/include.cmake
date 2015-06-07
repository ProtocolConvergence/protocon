
enable_testing ()
#include (CTest)

set (TestCwd ${TopPath})
set (MetaPath ${TopPath}/meta)
set (VerifPath ${CMAKE_CURRENT_SOURCE_DIR}/verif)

cat_parenthesized (TestNames "${CMAKE_CURRENT_SOURCE_DIR}/testlist.h")

## Unit tests.
foreach (testname ${TestNames})
  add_test (NAME ${testname}
    WORKING_DIRECTORY ${TestCwd}
    COMMAND test_exe ${testname})
endforeach ()

cat_parenthesized (DistribSpecs ${MetaPath}/examplespec.files)
cat_parenthesized (DistribSolns ${MetaPath}/examplesoln.files)

## Ensure that the specifications that we distribute can be parsed.
foreach (f ${DistribSpecs})
  add_test (NAME ofile_spec_${f}
    WORKING_DIRECTORY ${TestCwd}
    COMMAND "${CMAKE_COMMAND}"
    -Dprotocon_exe=$<TARGET_FILE:protocon>
    -Dxfile=examplespec/${f}.prot
    -P ${VerifPath}/ofile.cmake
    )
endforeach ()

## Ensure that the solutions that we distribute can be parsed.
foreach (f ${DistribSolns})
  add_test (NAME ofile_soln_${f}
    WORKING_DIRECTORY ${TestCwd}
    COMMAND "${CMAKE_COMMAND}"
    -Dprotocon_exe=$<TARGET_FILE:protocon>
    -Dxfile=examplesoln/${f}.prot
    -P ${VerifPath}/ofile.cmake
    )
endforeach ()

set (ExampleSpecs
  ColorRing
  ColorRingDistrib
  ColorRingSymm
  ColorTree
  ColorUniRing
  DiningCrypto
  DiningPhiloRand
  MatchRingOneBit
  MatchRingThreeState
  OldOrientRing
  OrientOddRing
  SortChain
  SumNotTarget
  TokenRingOdd
  TokenRingThreeBit
  )

foreach (f ${ExampleSpecs})
  add_test (NAME Synth3_${f}
    WORKING_DIRECTORY ${TestCwd}
    COMMAND protocon -x examplespec/${f}.prot -def N 3)
endforeach ()

foreach (f SortRing TokenRingDijkstra)
  list (APPEND ExampleSpecs ${f})
  add_test (NAME Synth_${f}
    WORKING_DIRECTORY ${TestCwd}
    COMMAND protocon -x examplespec/${f}.prot)
endforeach ()

foreach (f LeaderRingHuang)
  list (APPEND ExampleSpecs ${f})
  add_test (NAME SynthOpenMP_${f}
    WORKING_DIRECTORY ${TestCwd}
    COMMAND protocon -parallel 4 -x examplespec/${f}.prot)
  set_tests_properties (SynthOpenMP_${f} PROPERTIES PROCESSORS 4)

  if (MPI_FOUND)
    add_test (NAME SynthMPI_${f}
      WORKING_DIRECTORY ${TestCwd}
      COMMAND ${MPIEXEC} ${MPIEXEC_NUMPROC_FLAG} 4 ${MPIEXEC_PREFLAGS}
      ${BinPath}/protocon-mpi ${MPIEXEC_POSTFLAGS} -x examplespec/${f}.prot)
    set_tests_properties (SynthMPI_${f} PROPERTIES PROCESSORS 4)
  endif ()
endforeach ()

add_test (NAME Synth_Sat_sat
  WORKING_DIRECTORY ${TestCwd}
  COMMAND protocon -def ExpectSat 1 -x examplespec/Sat.prot)
add_test (NAME Synth_Sat_unsat
  WORKING_DIRECTORY ${TestCwd}
  COMMAND protocon -def ExpectSat 0 -x examplespec/Sat.prot)
set_tests_properties (Synth_Sat_unsat PROPERTIES WILL_FAIL TRUE)

list (APPEND ExampleSolns
  ${ExampleSpecs}
  DiningPhilo
  OrientRing
  OrientRingViaToken
  TokenChainDijkstra
  TokenRingFiveState
  TokenRingSixState
  TokenRingThreeState
  )

foreach (f ${ExampleSolns})
  add_test (NAME Verif5_${f}
    WORKING_DIRECTORY ${TestCwd}
    COMMAND protocon -verify -x examplesoln/${f}.prot -def N 5)
endforeach ()

add_test (NAME Verif_ByzantineGenerals
  WORKING_DIRECTORY ${TestCwd}
  COMMAND protocon -verify -x examplesoln/ByzantineGenerals.prot)

set (ExampleSynts
  LeaderRing
  MatchRing
  MatchRingOneBit
  OrientDaisy
  SegmentRing
  ShadowColorRing
  TokenChainDijkstra
  TokenRing
  TokenRingSuperpos
  TokenRingThreeBit
  TokenRingThreeState
  )

foreach (f ${ExampleSynts})
  add_test (NAME TrySynt_${f}
    WORKING_DIRECTORY ${TestCwd}
    COMMAND protocon -test -x examplespec/${f}.prot -x-try examplesynt/${f}.prot -def N 5)
  add_test (NAME VerifSynt_${f}
    WORKING_DIRECTORY ${TestCwd}
    COMMAND protocon -verify -x examplesynt/${f}.prot -def N 5)
  add_test (NAME overify_synt_${f}
    WORKING_DIRECTORY ${TestCwd}
    COMMAND "${CMAKE_COMMAND}"
    -Dprotocon_exe=$<TARGET_FILE:protocon>
    -Dxfile=examplesynt/${f}.prot
    -P ${VerifPath}/overify.cmake
    )
endforeach ()

add_test (NAME TrySynt2_TokenChainDijkstra
  WORKING_DIRECTORY ${TestCwd}
  COMMAND protocon -test -x examplespec/TokenChainDijkstra.prot
  -x-try examplesynt/TokenChainDijkstra.prot -def N 2)

add_test (NAME TrySynt5_TokenRingFourState
  WORKING_DIRECTORY ${TestCwd}
  COMMAND protocon -test -def M 2 -x examplespec/TokenRingSuperpos.prot
  -x-try examplesynt/TokenRingFourState.prot -def N 5)

list (APPEND VerifyBySynthesis
  ColorRing
  OrientDaisy
  OrientRing
  OrientOddRing
  TokenRingThreeBit
  )

foreach (f ${VerifyBySynthesis})
  add_test (NAME VerifSyn_${f}
    WORKING_DIRECTORY ${TestCwd}
    COMMAND protocon -x examplesoln/${f}.prot -def N 5)
endforeach ()

add_test (NAME Verif4_Sync_OrientRing
  WORKING_DIRECTORY ${TestCwd}
  COMMAND protocon -verify -synchronous -x examplesoln/OrientRing.prot -def N 4)

## Ensure our tests can actually detect failure.
add_test (NAME Verif4_OrientOddRing
  WORKING_DIRECTORY ${TestCwd}
  COMMAND protocon -verify -x examplesoln/OrientOddRing.prot -def N 4)
set_tests_properties (Verif4_OrientOddRing PROPERTIES WILL_FAIL TRUE)

