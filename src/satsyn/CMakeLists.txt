
#### Reduction-to-SAT Solver ####
# Not really used.

add_executable(satsyn
  "satsyn.c"
  "xnsys.c"
  )
set_property(TARGET satsyn APPEND PROPERTY INCLUDE_DIRECTORIES
  "${CMAKE_CURRENT_SOURCE_DIR}/.."
  "${LaceIncludeDir}")
target_link_libraries(satsyn cx_lib)
