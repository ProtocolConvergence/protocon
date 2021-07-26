# Stand-Alone UDP Executables
# Just for testing.

if (NOT UNIX OR APPLE)
  return()
endif ()


add_executable(udp_ThreeColorRing
  "act.h"
  "protocol.c"
  "protocol.h"
  )
set_property (TARGET udp_ThreeColorRing
  APPEND PROPERTY COMPILE_DEFINITIONS _POSIX_C_SOURCE=200112L)
target_link_libraries(udp_ThreeColorRing rt)

