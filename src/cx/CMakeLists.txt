
add_library (cx_lib STATIC
  "alphatab.c"
  "alphatab.h"
  "associa.h"
  "bittable.h"
  "bstree.c"
  "bstree.h"
  "def.h"
  "fileb.c"
  "fileb.h"
  "lgtable.h"
  "ofile.c"
  "ofile.h"
  "ospc.c"
  "ospc.h"
  "rbtree.c"
  "rbtree.h"
  "synhax.h"
  "syscx.c"
  "syscx.h"
  "table.h"
  "urandom.c"
  "urandom.h"
  "xfile.c"
  "xfile.h"
  )

set_property(TARGET cx_lib APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries (cx_lib fildesh_lib fildesh_compat_lib)

add_executable(bittable_test "bittable_test.c")
set_property(TARGET bittable_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries(bittable_test cx_lib)
add_test(NAME bittable_test COMMAND bittable_test)

add_executable(fileb_test "fileb_test.c")
set_property(TARGET fileb_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries(fileb_test cx_lib)
add_test(NAME fileb_test COMMAND fileb_test)

add_executable(lgtable_test "lgtable_test.c")
set_property(TARGET lgtable_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries(lgtable_test cx_lib)
add_test(NAME lgtable_test COMMAND lgtable_test)

add_executable(ospc_test "ospc_test.c")
set_property(TARGET ospc_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries(ospc_test cx_lib)
add_test(NAME ospc_test COMMAND ospc_test)

add_executable(rbtree_test "rbtree_test.c")
set_property(TARGET rbtree_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries(rbtree_test cx_lib)
add_test(NAME rbtree_test COMMAND rbtree_test)

add_executable(table_test "table_test.c")
set_property(TARGET table_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries(table_test cx_lib)
add_test(NAME table_test COMMAND table_test)

add_executable(tmpdir_test "tmpdir_test.c")
set_property(TARGET tmpdir_test APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}")
target_link_libraries(tmpdir_test cx_lib)
add_test(NAME tmpdir_test COMMAND tmpdir_test)

add_executable(testcxx "testcxx.cc")
set_property(TARGET testcxx APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}" "${CMAKE_SOURCE_DIR}/src")
target_link_libraries(testcxx cx_lib)
add_test(NAME testcxx COMMAND testcxx)
