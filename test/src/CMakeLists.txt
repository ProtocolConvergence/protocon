
include_directories("${CMAKE_SOURCE_DIR}")


add_executable(src_conflictfamily_test
  "conflictfamily_test.cc"
  )
target_link_libraries(src_conflictfamily_test protocon_lib)
add_test(NAME src_conflictfamily_test COMMAND
  "${CMAKE_COMMAND}" -E env "TEST_TMPDIR=${CMAKE_CURRENT_BINARY_DIR}" "$<TARGET_FILE:src_conflictfamily_test>")


add_executable(src_pcxn_test
  "pcxn_test.cc"
  )
target_link_libraries(src_pcxn_test protocon_lib ${M_LIB})
add_test(NAME src_pcxn_test COMMAND src_pcxn_test)

add_executable(src_stabilization_test
  "stabilization_test.cc"
  )
target_link_libraries(src_stabilization_test protocon_lib)
add_test(NAME src_stabilization_test COMMAND src_stabilization_test)

add_executable(src_xnsys_test
  "xnsys_test.cc"
  "${CMAKE_SOURCE_DIR}/src/inst.cc"
  )
target_link_libraries(src_xnsys_test xnsys_lib)
add_test(NAME src_xnsys_test COMMAND src_xnsys_test)

