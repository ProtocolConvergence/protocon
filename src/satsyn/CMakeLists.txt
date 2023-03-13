
#### Reduction-to-SAT Solver ####
# Not really used.

add_executable(satsyn
  "detect.c"
  "detect.h"
  "dimacs.h"
  "encodesat.c"
  "encodesat.h"
  "inst-sat3.h"
  "instance.c"
  "instance.h"
  "pla.c"
  "pla.h"
  "promela.c"
  "promela.h"
  "satsyn.c"
  "synsearch.c"
  "synsearch.h"
  "xnsys.c"
  "xnsys.h"
  )
set_property(TARGET satsyn APPEND PROPERTY INCLUDE_DIRECTORIES
  "${CMAKE_CURRENT_SOURCE_DIR}/.."
  "${LaceIncludeDir}")
target_link_libraries(satsyn cx_lib)
