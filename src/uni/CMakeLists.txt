
set (UniringBinPath ${CMAKE_CURRENT_BINARY_DIR}/uni)

#### Aperiodic Unidirectional Ring Protocol ####
addbinexe (uni-aperiodic uni/aperiodic.cc uni/unifile.cc)
set_target_properties (uni-aperiodic PROPERTIES
  OUTPUT_NAME aperiodic
  RUNTIME_OUTPUT_DIRECTORY ${UniringBinPath})

#### Generate Unidirectional Ring Protocols ####
addbinexe (uni-generate uni/generate.cc
  uni/canonical.cc
  uni/livelock.cc uni/unifile.cc
  pfmla-glu.c pfmla.c pfmla.cc)
set_property (TARGET uni-generate
  APPEND PROPERTY INCLUDE_DIRECTORIES ${GluIncludePath})
target_link_libraries (uni-generate cu glu cal ${M_LIB})
set_target_properties (uni-generate PROPERTIES
  OUTPUT_NAME generate
  RUNTIME_OUTPUT_DIRECTORY ${UniringBinPath})

#### Translate between Unidirectional Ring Protocol Representations ####
addbinexe (uni-xlate uni/xlate.cc
  uni/livelock.cc uni/unifile.cc)
set_target_properties (uni-xlate PROPERTIES
  OUTPUT_NAME xlate
  RUNTIME_OUTPUT_DIRECTORY ${UniringBinPath})

#### Classify Unidirectional Ring Protocols ####
addbinexe (uni-classify uni/classify.cc
  uni/livelock.cc uni/unifile.cc
  pfmla-glu.c pfmla.c pfmla.cc)
set_property (TARGET uni-classify
  APPEND PROPERTY INCLUDE_DIRECTORIES ${GluIncludePath})
target_link_libraries (uni-classify cu glu cal ${M_LIB})
set_target_properties (uni-classify PROPERTIES
  OUTPUT_NAME classify
  RUNTIME_OUTPUT_DIRECTORY ${UniringBinPath})

#### Unidirectional Ring Synthesis ####
addbinexe (uni-synthesize uni/synthesize.cc uni/unifile.cc ${ProtoconSources})
set_property (TARGET uni-synthesize
  APPEND PROPERTY INCLUDE_DIRECTORIES ${GluIncludePath})
#set_property (TARGET uni-synthesize
#  PROPERTY COMPILE_FLAGS "-Wextra -std=c++11")
#set_property (TARGET uni-synthesize
#  PROPERTY LINK_FLAGS "-Wextra -std=c++11")
#set_source_files_properties (${BldPath}/uni/synthesize.cc
#  PROPERTIES COMPILE_FLAGS "-Wextra -std=c++11")
target_link_libraries (uni-synthesize cu glu cal ${M_LIB})
set_target_properties (uni-synthesize PROPERTIES
  OUTPUT_NAME synthesize
  RUNTIME_OUTPUT_DIRECTORY ${UniringBinPath})

