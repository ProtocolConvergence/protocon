
enable_testing ()
#include (CTest)

set (TestPath ${TopPath}/test)
set (SpecPath ${TopPath}/examplespec)
set (SyntPath ${TopPath}/examplesynt)
set (SolnPath ${TopPath}/examplesoln)
set (SettPath ${TopPath}/examplesett)

set (MetaPath ${TopPath}/meta)
set (VerifPath ${CMAKE_CURRENT_SOURCE_DIR}/verif)

file(READ ${CMAKE_CURRENT_SOURCE_DIR}/testlist.txt TestNames)
string(REPLACE "\n" ";" TestNames "${TestNames}")

## Unit tests.
foreach (testname ${TestNames})
  add_test (NAME ${testname}
    WORKING_DIRECTORY ${TopPath}
    COMMAND test_exe ${testname})
endforeach ()

cat_parenthesized (DistribSpecs ${MetaPath}/examplespec.files)
cat_parenthesized (DistribSolns ${MetaPath}/examplesoln.files)

## Ensure that the specifications that we distribute can be parsed.
foreach (f ${DistribSpecs})
  add_test (NAME ofile_spec_${f}
    COMMAND "${CMAKE_COMMAND}"
    -Dprotocon_exe=${protocon_exe}
    -Dxfile=${SpecPath}/${f}.prot
    -P ${VerifPath}/ofile.cmake
    )
endforeach ()

## Ensure that the solutions that we distribute can be parsed.
foreach (f ${DistribSolns})
  add_test (NAME ofile_soln_${f}
    COMMAND "${CMAKE_COMMAND}"
    -Dprotocon_exe=${protocon_exe}
    -Dxfile=${SolnPath}/${f}.prot
    -P ${VerifPath}/ofile.cmake
    )
endforeach ()

set (ExampleSpecs
  ColorRing
  ColorRingDistrib
  ColorRingDizzy
  ColorRingLocal
  ColorTree
  ColorUniRing
  DiningCrypto
  DiningPhiloRand
  MatchRingOneBit
  MatchRingThreeState
  OldOrientRing
  OrientRingOdd
  SortChain
  SumNotTarget
  TokenRingOdd
  TokenRingRand
  TokenRingThreeBit
  )

# Specifications that have solutions
# with different names.
set (GenericSpecs
  MatchRing
  TokenChain
  TokenRing
  TokenRingSuperpos
  )

foreach (f ${ExampleSpecs} ${GenericSpecs})
  add_test (NAME Synth3_${f}
    COMMAND protocon -x ${SpecPath}/${f}.prot -param N 3)
endforeach ()

foreach (f SortRing TokenRingDijkstra)
  list (APPEND ExampleSpecs ${f})
  add_test (NAME Synth_${f}
    COMMAND protocon -x ${SpecPath}/${f}.prot)
endforeach ()

foreach (f LeaderRingHuang)
  list (APPEND ExampleSpecs ${f})
  add_test (NAME SynthOpenMP_${f}
    COMMAND protocon -parallel 4 -x ${SpecPath}/${f}.prot -prep-conflicts)
  set_tests_properties (SynthOpenMP_${f} PROPERTIES PROCESSORS 4)

  if (MPI_FOUND)
    add_test (NAME SynthMPI_${f}
      COMMAND ${MPIEXEC} ${MPIEXEC_NUMPROC_FLAG} 4 ${MPIEXEC_PREFLAGS}
      ${BinPath}/protocon-mpi ${MPIEXEC_POSTFLAGS} -x ${SpecPath}/${f}.prot -prep-conflicts)
    set_tests_properties (SynthMPI_${f} PROPERTIES PROCESSORS 4)
  endif ()
endforeach ()

add_test (NAME Synth_Sat_sat
  COMMAND protocon -def ExpectSat 1 -x ${SpecPath}/Sat.prot)
add_test (NAME Synth_Sat_unsat
  COMMAND protocon -def ExpectSat 0 -x ${SpecPath}/Sat.prot)
set_tests_properties (Synth_Sat_unsat PROPERTIES WILL_FAIL TRUE)

list (APPEND ExampleSolns
  ${ExampleSpecs}
  DiningPhilo
  OrientRing
  OrientRingViaToken
  TokenChainDijkstra
  TokenChainThreeState
  TokenRingFiveState
  TokenRingSixState
  TokenRingThreeState
  )

foreach (f ${ExampleSolns})
  add_test (NAME Verif5_${f}
    COMMAND protocon -verify -x ${SolnPath}/${f}.prot -param N 5)
endforeach ()

add_test (NAME Verif_ByzantineGenerals
  COMMAND protocon -verify -x ${SolnPath}/ByzantineGenerals.prot)

set (ExampleSynts
  ColorRing
  LeaderRing
  MatchRing
  MatchRingOneBit
  OrientDaisy
  SegmentRing
  ShadowColorRing
  TokenChain
  TokenChainDijkstra
  TokenRing
  TokenRingSuperpos
  TokenRingThreeBit
  TokenRingThreeState
  )

foreach (f ${ExampleSynts})
  add_test (NAME TrySynt_${f}
    COMMAND protocon -test -x ${SpecPath}/${f}.prot -x-try-subset ${SyntPath}/${f}.prot -param N 5)
  add_test (NAME VerifSynt_${f}
    COMMAND protocon -verify -x ${SyntPath}/${f}.prot -param N 5)
  add_test (NAME overify_synt_${f}
    COMMAND "${CMAKE_COMMAND}"
    -Dprotocon_exe=${protocon_exe}
    -Dxfile=${SyntPath}/${f}.prot
    -P ${VerifPath}/overify.cmake
    )
endforeach ()

add_test (NAME TrySynt2_TokenChainDijkstra
  COMMAND protocon -test -x ${SpecPath}/TokenChainDijkstra.prot
  -x-try-subset ${SyntPath}/TokenChainDijkstra.prot -param N 2)

add_test (NAME TrySynt5_TokenRingFourState
  COMMAND protocon -test -def M 2 -x ${SpecPath}/TokenRingSuperpos.prot
  -x-try-subset ${SyntPath}/TokenRingFourState.prot -param N 5)

set (VerifyBySynthesis
  ColorRing
  OrientDaisy
  TokenRingThreeBit
  )

foreach (f ${VerifyBySynthesis})
  add_test (NAME VerifSyn_${f}
    COMMAND protocon -x ${SolnPath}/${f}.prot -param N 5)
endforeach ()

foreach (f LeaderTree)
  add_test (NAME Synth_${f}
    COMMAND protocon -x-args ${SettPath}/${f}.args)
  add_test (NAME TrySynt_${f}
    COMMAND protocon -test
    -x-args ${SettPath}/${f}.args
    -x-try-subset ${SolnPath}/${f}.prot)
endforeach ()


set (VerifyBySynthesis
  OrientRing
  OrientRingOdd
  )
foreach (f ${VerifyBySynthesis})
  add_test (NAME VerifSyn_${f}
    COMMAND protocon -x ${SolnPath}/${f}.prot -param N 5)
endforeach ()

add_test (NAME Verif4_Sync_OrientRing
  COMMAND protocon -verify -synchronous -x ${SolnPath}/OrientRing.prot -param N 4)


## Promela file output.
add_test (NAME Promela_OrientDaisy
  COMMAND comparispawn ${TestPath}/expect/OrientDaisy.pml
  ${protocon_exe} -nop -x ${SolnPath}/OrientDaisy.prot -param N 5 -o-pml -)

## Ensure our tests can actually detect failure.
add_test (NAME Verif4_OrientRingOdd
  COMMAND protocon -verify -x ${SolnPath}/OrientRingOdd.prot -param N 4)
set_tests_properties (Verif4_OrientRingOdd PROPERTIES WILL_FAIL TRUE)

