
add_library (cx_lib STATIC
  "alphatab.c"
  "alphatab.h"
  "bittable.h"
  "def.h"
  "fileb.c"
  "fileb.h"
  "lgtable.h"
  "ofile.c"
  "ofile.h"
  "synhax.h"
  "syscx.c"
  "syscx.h"
  "table.h"
  "urandom.c"
  "urandom.h"
  "xfile.c"
  "xfile.h"
  )

target_link_libraries (cx_lib fildesh_lib fildesh_compat_lib)

add_executable(bittable_test "bittable_test.c")
target_link_libraries(bittable_test cx_lib)
add_test(NAME bittable_test COMMAND bittable_test)

add_executable(fileb_test "fileb_test.c")
target_link_libraries(fileb_test cx_lib)
add_test(NAME fileb_test COMMAND fileb_test)

add_executable(lgtable_test "lgtable_test.c")
target_link_libraries(lgtable_test cx_lib)
add_test(NAME lgtable_test COMMAND lgtable_test)

add_executable(table_test "table_test.c")
target_link_libraries(table_test cx_lib)
add_test(NAME table_test COMMAND table_test)

add_executable(tmpdir_test "tmpdir_test.c")
target_link_libraries(tmpdir_test cx_lib)
add_test(NAME tmpdir_test COMMAND tmpdir_test)

add_executable(testcxx "testcxx.cc")
target_link_libraries(testcxx cx_lib)
add_test(NAME testcxx COMMAND testcxx)
