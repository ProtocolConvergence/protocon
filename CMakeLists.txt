
cmake_minimum_required (VERSION 2.8)
#set(CMAKE_DISABLE_SOURCE_CHANGES ON)
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)

project (protocon)

#SET(CMAKE_CXX_FLAGS_DEBUG "-g3")
#SET(CMAKE_C_FLAGS_DEBUG "-g3")
#set (CMAKE_BUILD_TYPE DEBUG)
#set (CMAKE_BUILD_TYPE RELEASE)
#set (CMAKE_BUILD_TYPE RelWithDebInfo)

include(ExternalProject)

ExternalProject_Add(peg_project
  URL "https://github.com/gpakosz/peg/archive/0.1.18.tar.gz"
  URL_HASH SHA256=aa25b2e10cc673a0a6f20114b0dc5cfc6ce221d1c257852fe4128f0782cbb585
  BUILD_IN_SOURCE 1
  UPDATE_COMMAND echo "No update."
  CONFIGURE_COMMAND echo "No configure step."
  INSTALL_COMMAND echo "No install step."
  )

ExternalProject_Get_Property(peg_project SOURCE_DIR)
set (peg_exe "${SOURCE_DIR}/leg")


enable_testing ()

add_subdirectory(src)
