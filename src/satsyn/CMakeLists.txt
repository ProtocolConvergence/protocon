
#### Reduction-to-SAT Solver ####
# Not really used.

string(REGEX REPLACE "-DNDEBUG " "" CMAKE_C_FLAGS "${CMAKE_C_FLAGS}")

add_executable(satsyn
  "satsyn.c"
  "xnsys.c"
  )
set_property(TARGET satsyn APPEND PROPERTY INCLUDE_DIRECTORIES
  "${CMAKE_CURRENT_SOURCE_DIRECTORY}/../"
  "${LaceIncludeDir}" "${LaceCxIncludePath}")
target_link_libraries(satsyn lace_cx_lib)
