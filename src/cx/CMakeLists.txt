
#string(REGEX REPLACE "-DNDEBUG " "" CMAKE_C_FLAGS "${CMAKE_C_FLAGS}")

add_executable(testcxx
  "testcxx.cc")
set_property(TARGET testcxx APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceCxIncludePath}")
target_link_libraries(testcxx lace_cx_lib)

add_test(NAME testcxx COMMAND testcxx)
