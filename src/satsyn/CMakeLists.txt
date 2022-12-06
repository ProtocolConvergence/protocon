
#### Reduction-to-SAT Solver ####
# Not really used.

add_executable(satsyn
  "detect.c"
  "encodesat.c"
  "instance.c"
  "promela.c"
  "satsyn.c"
  "synsearch.c"
  "xnsys.c"
  )
set_property(TARGET satsyn APPEND PROPERTY INCLUDE_DIRECTORIES
  "${CMAKE_CURRENT_SOURCE_DIR}/.."
  "${LaceIncludeDir}")
target_link_libraries(satsyn cx_lib)
