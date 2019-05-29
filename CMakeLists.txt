
cmake_minimum_required (VERSION 2.8)
#set(CMAKE_DISABLE_SOURCE_CHANGES ON)
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)

include(ExternalProject)

set (GluPfx mdd-glu)
set (PegPfx peg)

set (TopPath ${CMAKE_CURRENT_SOURCE_DIR})
set (DepPath ${TopPath}/dep)
set (BinPath ${TopPath}/bin)

ExternalProject_Add(cx
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/cx
  SOURCE_DIR ${DepPath}/cx/src
  BINARY_DIR ${DepPath}/cx/bld
  BUILD_ALWAYS 1
  INSTALL_COMMAND echo "No install step."
  )

ExternalProject_Add(peg
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/peg
  SOURCE_DIR ${DepPath}/${PegPfx}
  BUILD_IN_SOURCE 1
  UPDATE_COMMAND echo "No update."
  CONFIGURE_COMMAND echo "No configure step."
  INSTALL_COMMAND echo "No install step."
  )

ExternalProject_Add(glu
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/mdd-glu
  SOURCE_DIR ${DepPath}/${GluPfx}/src
  BINARY_DIR ${DepPath}/${GluPfx}/bld
  BUILD_ALWAYS 1
  INSTALL_COMMAND ${CMAKE_COMMAND} -E make_directory ${DepPath}/${GluPfx}/bld/include
  COMMAND ${CMAKE_COMMAND} -E copy_if_different
  ${DepPath}/${GluPfx}/src/array/array.h
  ${DepPath}/${GluPfx}/src/avl/avl.h
  ${DepPath}/${GluPfx}/src/epd/epd.h
  ${DepPath}/${GluPfx}/src/bdd/bdd.h
  ${DepPath}/${GluPfx}/src/mdd/mdd.h
  ${DepPath}/${GluPfx}/src/util/util.h
  ${DepPath}/${GluPfx}/src/st/st.h
  ${DepPath}/${GluPfx}/src/var_set/var_set.h
  ${DepPath}/${GluPfx}/bld/include/
  )

ExternalProject_Add(protocon
  DEPENDS cx peg glu
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external/src
  SOURCE_DIR ${TopPath}/src
  BINARY_DIR ${TopPath}/bld
  BUILD_ALWAYS 1
  CONFIGURE_COMMAND ${CMAKE_COMMAND}
  -D peg_exe:string=${DepPath}/${PegPfx}/leg
  -D GluBldPath:string=${DepPath}/${GluPfx}/bld
  ../src
  INSTALL_COMMAND echo "No install step."
  )

