
cmake_minimum_required (VERSION 2.8)
#set(CMAKE_DISABLE_SOURCE_CHANGES ON)
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)

include(ExternalProject)

set (GluPfx glu-2.4)
set (PegPfx peg-0.1.15)

set (TopPath ${CMAKE_CURRENT_SOURCE_DIR})
set (DepPath ${TopPath}/dep)
set (BinPath ${TopPath}/bin)

ExternalProject_Add(cx-pp
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/cx-pp
  SOURCE_DIR ${DepPath}/cx-pp
  #GIT_REPOSITORY git@github.com:grencez/cx-pp.git
  BUILD_IN_SOURCE 1
  CONFIGURE_COMMAND echo "No configure step."
  BUILD_COMMAND echo "No build step."
  INSTALL_COMMAND echo "No install step."
  )

ExternalProject_Add(cx
  DEPENDS cx-pp
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/cx
  SOURCE_DIR ${DepPath}/cx/src
  CONFIGURE_COMMAND ${CMAKE_COMMAND}
  -D BinPath:string=${BinPath}
  ${DepPath}/cx/src
  #BINARY_DIR ${DepPath}/cx/bld
  #GIT_REPOSITORY git@github.com:grencez/cx.git
  INSTALL_COMMAND echo "No install step."
  )

ExternalProject_Add(peg
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/peg
  SOURCE_DIR ${DepPath}/${PegPfx}
  URL http://piumarta.com/software/peg/${PegPfx}.tar.gz
  BUILD_IN_SOURCE 1
  CONFIGURE_COMMAND echo "No configure step."
  INSTALL_COMMAND echo "No install step."
  )

ExternalProject_Add(glu
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/glu
  SOURCE_DIR ${DepPath}/${GluPfx}
  URL ftp://vlsi.colorado.edu/pub/vis/${GluPfx}.tar.gz
  BUILD_IN_SOURCE 1
  CONFIGURE_COMMAND ./configure --enable-gcc
  INSTALL_COMMAND echo "No install step."
  )

ExternalProject_Add(protocon
  DEPENDS cx peg glu
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/src
  SOURCE_DIR ${TopPath}/src
  BINARY_DIR ${TopPath}/bld
  CONFIGURE_COMMAND ${CMAKE_COMMAND}
  -D PegExe:string=${DepPath}/${PegPfx}/leg
  -D GluPath:string=${DepPath}/${GluPfx}
  ../src
  INSTALL_COMMAND echo "No install step."
  )

