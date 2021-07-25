
cmake_minimum_required (VERSION 2.8.12)
#set(CMAKE_DISABLE_SOURCE_CHANGES ON)
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)

project (protocon)

#SET(CMAKE_CXX_FLAGS_DEBUG "-g3")
#SET(CMAKE_C_FLAGS_DEBUG "-g3")
#set (CMAKE_BUILD_TYPE DEBUG)
#set (CMAKE_BUILD_TYPE RELEASE)
#set (CMAKE_BUILD_TYPE RelWithDebInfo)

if (NOT CMAKE_BUILD_TYPE)
  set (CMAKE_BUILD_TYPE Release)
endif()

# Keep assertions enabled.
string(REPLACE "-DNDEBUG" "" CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE}")
string(REPLACE "/DNDEBUG" "" CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE}")
string(REPLACE "-DNDEBUG" "" CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE}")
string(REPLACE "/DNDEBUG" "" CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE}")


include(ExternalProject)


ExternalProject_Add(lace_project
  GIT_REPOSITORY "https://github.com/grencez/lace.git"
  GIT_TAG "ff5e32305222ffcfa4b3d6df3be5c15c3174909d"
  #GIT_TAG "trunk"
  CMAKE_ARGS "-DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>"
  BUILD_BYPRODUCTS
  "<BINARY_DIR>/compat/liblace_compat_lib.a"
  "<BINARY_DIR>/src/liblace_lib.a"
  "<BINARY_DIR>/tool/cembed"
  "<BINARY_DIR>/tool/comparispawn"
  "<BINARY_DIR>/tool/cswitch"
  )
add_executable(lace IMPORTED)
add_executable(cembed IMPORTED)
add_executable(comparispawn IMPORTED)
add_executable(cswitch IMPORTED)
add_library (lace_lib STATIC IMPORTED)
add_library (lace_compat_lib STATIC IMPORTED)
ExternalProject_Get_Property(lace_project INSTALL_DIR)
set_target_properties(lace PROPERTIES IMPORTED_LOCATION "${INSTALL_DIR}/bin/lace")
ExternalProject_Get_Property(lace_project BINARY_DIR)
set_target_properties(cembed PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/tool/cembed")
set_target_properties(comparispawn PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/tool/comparispawn")
set_target_properties(cswitch PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/tool/cswitch")
set_target_properties(lace_lib PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/src/liblace_lib.a")
set_target_properties(lace_compat_lib PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/compat/liblace_compat_lib.a")
add_dependencies (lace lace_project)
add_dependencies (lace_lib lace_project)
add_dependencies (lace_compat_lib lace_project)
add_dependencies (cembed lace_project)
add_dependencies (comparispawn lace_project)
add_dependencies (cswitch lace_project)
ExternalProject_Get_Property(lace_project SOURCE_DIR)
set (LaceIncludeDir "${SOURCE_DIR}/include")


ExternalProject_Add(mdd_glu_project
  GIT_REPOSITORY "https://github.com/grencez/mdd-glu.git"
  GIT_TAG "2d00c406296ecc505d4aaa2cb4628fc5c441e011"
  CMAKE_ARGS "-DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>"
  )
add_library (mdd_cu_lib STATIC IMPORTED)
add_library (mdd_glu_lib STATIC IMPORTED)
ExternalProject_Get_Property(mdd_glu_project INSTALL_DIR)
set_target_properties(mdd_cu_lib PROPERTIES IMPORTED_LOCATION "${INSTALL_DIR}/lib/libcu.a")
set_target_properties(mdd_glu_lib PROPERTIES IMPORTED_LOCATION "${INSTALL_DIR}/lib/libglu.a")
add_dependencies (mdd_cu_lib mdd_glu_project)
add_dependencies (mdd_glu_lib mdd_glu_project)
list (APPEND mdd_glu_libs mdd_cu_lib mdd_glu_lib)
set (GluIncludePath "${INSTALL_DIR}/include")


ExternalProject_Add(peg_project
  URL "https://github.com/gpakosz/peg/archive/0.1.18.tar.gz"
  URL_HASH SHA256=aa25b2e10cc673a0a6f20114b0dc5cfc6ce221d1c257852fe4128f0782cbb585
  BUILD_IN_SOURCE 1
  CONFIGURE_COMMAND echo "No configure step."
  INSTALL_COMMAND echo "No install step."
  )
add_executable(peg_leg IMPORTED)
ExternalProject_Get_Property(peg_project SOURCE_DIR)
set_target_properties(peg_leg PROPERTIES IMPORTED_LOCATION "${SOURCE_DIR}/leg")
add_dependencies (peg_leg peg_project)


enable_testing ()

add_subdirectory(src)
add_subdirectory(test)
