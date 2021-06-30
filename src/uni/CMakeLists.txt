

#### Aperiodic Unidirectional Ring Protocol ####
add_executable(uni_aperiodic
  "aperiodic.cc"
  "uniact.hh"
  "unifile.cc"
  "unifile.hh"
  )
set_property(TARGET uni_aperiodic APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}" "${CMAKE_CURRENT_SOURCE_DIR}/..")
set_target_properties(uni_aperiodic PROPERTIES
  OUTPUT_NAME "aperiodic")
target_link_libraries(uni_aperiodic cx_lib)


#### Generate Unidirectional Ring Protocols ####
add_executable(uni_generate
  "generate.cc"
  "adjlist.hh"
  "canonical.cc"
  "canonical.hh"
  "livelock.cc"
  "livelock.hh"
  "uniact.hh"
  "unifile.cc"
  "unifile.hh"
  )
set_property(TARGET uni_generate APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}" "${CMAKE_CURRENT_SOURCE_DIR}/..")
set_target_properties(uni_generate PROPERTIES
  OUTPUT_NAME "generate")
target_link_libraries(uni_generate pfmla_lib)


#### Translate between Unidirectional Ring Protocol Representations ####
add_executable(uni_xlate
  "xlate.cc"
  "adjlist.hh"
  "livelock.cc"
  "livelock.hh"
  "uniact.hh"
  "unifile.cc"
  "unifile.hh"
  )
set_property(TARGET uni_xlate APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}" "${CMAKE_CURRENT_SOURCE_DIR}/..")
set_target_properties(uni_xlate PROPERTIES
  OUTPUT_NAME "xlate")
target_link_libraries(uni_xlate prot_file_lib)


#### Classify Unidirectional Ring Protocols ####
add_executable(uni_classify
  "xlate.cc"
  "adjlist.hh"
  "livelock.cc"
  "livelock.hh"
  "uniact.hh"
  "unifile.cc"
  "unifile.hh"
  )
set_property(TARGET uni_classify APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}" "${CMAKE_CURRENT_SOURCE_DIR}/..")
set_target_properties(uni_classify PROPERTIES
  OUTPUT_NAME "classify")
target_link_libraries(uni_classify pfmla_lib)


#### Unidirectional Ring Synthesis ####
add_executable(uni_synthesize
  "synthesize.cc"
  "adjlist.hh"
  "uniact.hh"
  "unifile.cc"
  "unifile.hh"
  )
set_property(TARGET uni_synthesize APPEND PROPERTY INCLUDE_DIRECTORIES
  "${LaceIncludeDir}" "${CMAKE_CURRENT_SOURCE_DIR}/..")
set_target_properties(uni_synthesize PROPERTIES
  OUTPUT_NAME "synthesize")
target_link_libraries(uni_synthesize prot_file_lib)
#set_property (TARGET uni_synthesize
#  PROPERTY COMPILE_FLAGS "-Wextra -std=c++11")
#set_property (TARGET uni_synthesize
#  PROPERTY LINK_FLAGS "-Wextra -std=c++11")
#set_source_files_properties ("synthesize.cc"
#  PROPERTIES COMPILE_FLAGS "-Wextra -std=c++11")
