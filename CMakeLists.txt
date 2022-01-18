
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


ExternalProject_Add(fildesh_project
  GIT_REPOSITORY "https://github.com/fildesh/fildesh.git"
  GIT_TAG "d49068e4e4e83a50d3089dfae147f498be0dfd85"
  #GIT_TAG "trunk"
  CMAKE_ARGS "-DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>"
  BUILD_BYPRODUCTS
  "<BINARY_DIR>/compat/libfildesh_compat_lib.a"
  "<BINARY_DIR>/src/libfildesh_lib.a"
  "<BINARY_DIR>/tool/cembed"
  "<BINARY_DIR>/tool/comparispawn"
  "<BINARY_DIR>/tool/cswitch"
  )
add_executable(fildesh IMPORTED)
add_executable(cembed IMPORTED)
add_executable(comparispawn IMPORTED)
add_executable(cswitch IMPORTED)
add_library (fildesh_lib STATIC IMPORTED)
add_library (fildesh_compat_lib STATIC IMPORTED)
ExternalProject_Get_Property(fildesh_project INSTALL_DIR)
set_target_properties(fildesh PROPERTIES IMPORTED_LOCATION "${INSTALL_DIR}/bin/fildesh")
ExternalProject_Get_Property(fildesh_project BINARY_DIR)
set_target_properties(cembed PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/tool/cembed")
set_target_properties(comparispawn PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/tool/comparispawn")
set_target_properties(cswitch PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/tool/cswitch")
set_target_properties(fildesh_lib PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/src/libfildesh_lib.a")
set_target_properties(fildesh_compat_lib PROPERTIES IMPORTED_LOCATION "${BINARY_DIR}/compat/libfildesh_compat_lib.a")
add_dependencies (fildesh fildesh_project)
add_dependencies (fildesh_lib fildesh_project)
add_dependencies (fildesh_compat_lib fildesh_project)
add_dependencies (cembed fildesh_project)
add_dependencies (comparispawn fildesh_project)
add_dependencies (cswitch fildesh_project)
ExternalProject_Get_Property(fildesh_project SOURCE_DIR)
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

#### Build ####
add_subdirectory(src)

#### Test ####
# (The src/ subdirectory has some tests too.)
add_subdirectory(test)

#### Install ####
# (The src/ subdirectory installed some stuff too.)
install(DIRECTORY "${CMAKE_SOURCE_DIR}/doc/" DESTINATION doc)
install(DIRECTORY "${CMAKE_SOURCE_DIR}/example/" DESTINATION example)

# Build a CPack-driven installer package.
#   cpack --config CPackConfig.cmake
# Or just:
#   cpack
include(InstallRequiredSystemLibraries)
string(TIMESTAMP CPACK_PACKAGE_VERSION "%Y%m%d")
#set(CPACK_PACKAGE_VERSION "20210725")
set(CPACK_GENERATOR "ZIP")
#set(CPACK_GENERATOR "STGZ;TGZ;ZIP")
set(MyName "Alex Klinkhamer")
set(CPACK_PACKAGE_VENDOR ${MyName})
set(CPACK_PACKAGE_CONTACT ${MyName})
set(CPACK_RESOURCE_FILE_LICENSE "${CMAKE_SOURCE_DIR}/LICENSE")
include(CPack)
