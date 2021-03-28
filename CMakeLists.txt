
cmake_minimum_required (VERSION 2.8.12)
#set(CMAKE_DISABLE_SOURCE_CHANGES ON)
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)

project (protocon)

#SET(CMAKE_CXX_FLAGS_DEBUG "-g3")
#SET(CMAKE_C_FLAGS_DEBUG "-g3")
#set (CMAKE_BUILD_TYPE DEBUG)
#set (CMAKE_BUILD_TYPE RELEASE)
#set (CMAKE_BUILD_TYPE RelWithDebInfo)


include(ExternalProject)


ExternalProject_Add(lace_project
  GIT_REPOSITORY "https://github.com/grencez/lace.git"
  GIT_TAG "19d31b460c4ea6d628336ee4cdd479112da325a6"
  #GIT_TAG "trunk"
  CMAKE_ARGS "-DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>"
  BUILD_BYPRODUCTS
  "<BINARY_DIR>/src/cx/libcx_lib.a"
  "<BINARY_DIR>/tool/cembed"
  "<BINARY_DIR>/tool/comparispawn"
  "<BINARY_DIR>/tool/cswitch"
  )
add_executable(lace IMPORTED)
add_executable(cembed IMPORTED)
add_executable(comparispawn IMPORTED)
add_executable(cswitch IMPORTED)
add_library (lace_cx_lib STATIC IMPORTED)
ExternalProject_Get_Property(lace_project INSTALL_DIR)
set_target_properties(lace PROPERTIES IMPORTED_LOCATION "${INSTALL_DIR}/bin/lace")
ExternalProject_Get_Property(lace_project BINARY_DIR)
set_target_properties(cembed PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/tool/cembed")
set_target_properties(comparispawn PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/tool/comparispawn")
set_target_properties(cswitch PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/tool/cswitch")
set_target_properties(lace_cx_lib PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/src/cx/libcx_lib.a")
add_dependencies (lace lace_project)
add_dependencies (lace_cx_lib lace_project)
add_dependencies (cembed lace_project)
add_dependencies (comparispawn lace_project)
add_dependencies (cswitch lace_project)
ExternalProject_Get_Property(lace_project SOURCE_DIR)
set (LaceCxIncludePath "${SOURCE_DIR}/src")
set (LaceIncludeDir "${SOURCE_DIR}/include")


ExternalProject_Add(mdd_glu_project
  GIT_REPOSITORY "https://github.com/grencez/mdd-glu.git"
  GIT_TAG "fce409f88b24385a5fbc521709186b96f13b5383"
  CMAKE_ARGS "-DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>"
  )
add_library (mdd_cu_lib STATIC IMPORTED)
add_library (mdd_glu_lib STATIC IMPORTED)
add_library (mdd_cal_lib STATIC IMPORTED)
ExternalProject_Get_Property(mdd_glu_project INSTALL_DIR)
set_target_properties(mdd_cu_lib PROPERTIES IMPORTED_LOCATION "${INSTALL_DIR}/lib/libcu.a")
set_target_properties(mdd_glu_lib PROPERTIES IMPORTED_LOCATION "${INSTALL_DIR}/lib/libglu.a")
set_target_properties(mdd_cal_lib PROPERTIES IMPORTED_LOCATION "${INSTALL_DIR}/lib/libcal.a")
add_dependencies (mdd_cu_lib mdd_glu_project)
add_dependencies (mdd_glu_lib mdd_glu_project)
add_dependencies (mdd_cal_lib mdd_glu_project)
list (APPEND mdd_glu_libs mdd_cu_lib mdd_glu_lib mdd_cal_lib)
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
