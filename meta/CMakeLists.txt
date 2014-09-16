
cmake_minimum_required (VERSION 2.8)
#set(CMAKE_DISABLE_SOURCE_CHANGES ON)
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)

include(ExternalProject)

set (GluPfx glu-2.4)
set (PegPfx peg-0.1.15)

ExternalProject_Add(glu
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/glu
  SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/${GluPfx}
  URL ftp://vlsi.colorado.edu/pub/vis/${GluPfx}.tar.gz
  BUILD_IN_SOURCE 1
  CONFIGURE_COMMAND ./configure --enable-gcc
  INSTALL_COMMAND echo "No install step."
  )


ExternalProject_Add(peg
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/peg
  SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/${PegPfx}
  URL http://piumarta.com/software/peg/${PegPfx}.tar.gz
  BUILD_IN_SOURCE 1
  CONFIGURE_COMMAND echo "No configure step."
  INSTALL_COMMAND echo "No install step."
  )

ExternalProject_Add(cx
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/cx
  SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/cx
  BINARY_DIR ${CMAKE_CURRENT_SOURCE_DIR}/cx/bld
  INSTALL_COMMAND echo "No install step."
  )

ExternalProject_Add(protocon
  DEPENDS cx peg glu
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/protocon
  SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/protocon
  BINARY_DIR ${CMAKE_CURRENT_SOURCE_DIR}/protocon/bld
  CONFIGURE_COMMAND ${CMAKE_COMMAND} -D PegExe:string=${CMAKE_CURRENT_SOURCE_DIR}/${PegPfx}/leg ..
  INSTALL_COMMAND echo "No install step."
  )

