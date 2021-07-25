
set (protocon_exe "$<TARGET_FILE:protocon>")

add_test (NAME Verif4_Sync_OrientRing_test COMMAND lace -alias "protocon=${protocon_exe}" -f
  "${CMAKE_CURRENT_SOURCE_DIR}/Verif4_Sync_OrientRing_test.lace"
  "${CMAKE_SOURCE_DIR}/examplesoln/OrientRing.prot")

## Ensure our tests can actually detect failure.
add_test (NAME Verif4_OrientRingOdd_failure_test COMMAND lace -alias "protocon=${protocon_exe}" -f
  "${CMAKE_CURRENT_SOURCE_DIR}/Verif4_OrientRingOdd_failure_test.lace"
  "${CMAKE_SOURCE_DIR}/examplesoln/OrientRingOdd.prot")
set_tests_properties (Verif4_OrientRingOdd_failure_test PROPERTIES WILL_FAIL TRUE)

## PLA file output.
add_test (NAME PLA_MatchRingThreeState_test COMMAND lace -alias "protocon=${protocon_exe}" -f
  "${CMAKE_CURRENT_SOURCE_DIR}/PLA_MatchRingThreeState_test.lace"
  "${CMAKE_CURRENT_SOURCE_DIR}/MatchRingThreeState.pla"
  "${CMAKE_SOURCE_DIR}/examplesoln/MatchRingThreeState.prot")

## Promela file output.
add_test (NAME Promela_OrientDaisy_test COMMAND lace -alias "protocon=${protocon_exe}" -f
  "${CMAKE_CURRENT_SOURCE_DIR}/Promela_OrientDaisy_test.lace"
  "${CMAKE_CURRENT_SOURCE_DIR}/OrientDaisy.pml"
  "${CMAKE_SOURCE_DIR}/examplesoln/OrientDaisy.prot")

## UDP file output.
add_test (NAME UDP_TokenRingRand_test COMMAND lace -alias "protocon=${protocon_exe}" -f
  "${CMAKE_CURRENT_SOURCE_DIR}/UDP_TokenRingRand_test.lace"
  "${CMAKE_CURRENT_SOURCE_DIR}/TokenRingRand.h"
  "${CMAKE_SOURCE_DIR}/examplesoln/TokenRingRand.prot")
