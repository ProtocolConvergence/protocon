
cmake_minimum_required(VERSION 3.14)
# CMake 3.8 for C++17.
# CMake 3.14 for FetchContent_MakeAvailable().

#set(CMAKE_DISABLE_SOURCE_CHANGES ON)
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)
project(Protocon LANGUAGES "C" "CXX")
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_CXX_STANDARD 17)

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

include(CTest)

include(FetchContent)
include("dep/cmake_fetchcontent/fildesh.cmake")
include("dep/cmake_fetchcontent/mddglu.cmake")

include(ExternalProject)
include("dep/cmake_externalproject/peg.cmake")

#### Build ####
include_directories(
  "${PROJECT_SOURCE_DIR}"
  ${Fildesh_INCLUDE_DIRS}
)
add_subdirectory(src)

#### Test ####
# (The src/ subdirectory has some tests too.)
if (BUILD_TESTING)
  add_subdirectory(test)
endif()

#### Install ####
# (The src/ subdirectory installed some stuff too.)
install(DIRECTORY "${PROJECT_SOURCE_DIR}/doc/" DESTINATION doc)
install(DIRECTORY "${PROJECT_SOURCE_DIR}/example/" DESTINATION example)

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
set(CPACK_RESOURCE_FILE_LICENSE "${PROJECT_SOURCE_DIR}/LICENSE")
include(CPack)
