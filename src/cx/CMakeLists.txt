
add_library (cx_lib STATIC
  "bittable.h"
  "def.h"
  "lgtable.h"
  "synhax.h"
  "syscx.c"
  "table.h"
  "urandom.c"
  "urandom.h"
  )

target_link_libraries (cx_lib ${Fildesh_LIBRARIES})

add_executable(bittable_test "bittable_test.c")
target_link_libraries(bittable_test cx_lib)
add_test(NAME bittable_test COMMAND bittable_test)

add_executable(lgtable_test "lgtable_test.c")
target_link_libraries(lgtable_test cx_lib)
add_test(NAME lgtable_test COMMAND lgtable_test)

add_executable(table_test "table_test.c")
target_link_libraries(table_test cx_lib)
add_test(NAME table_test COMMAND table_test)

add_executable(testcxx "testcxx.cc")
target_link_libraries(testcxx cx_lib)
add_test(NAME testcxx COMMAND testcxx)
