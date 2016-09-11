
set (UniringBinPath ${CMAKE_CURRENT_BINARY_DIR}/uni)

#### Aperiodic Unidirectional Ring Protocol ####
addbinexe (uni_aperiodic uni/aperiodic.cc uni/unifile.cc)
set_target_properties (uni_aperiodic PROPERTIES
  OUTPUT_NAME aperiodic
  RUNTIME_OUTPUT_DIRECTORY ${UniringBinPath})

#### Generate Unidirectional Ring Protocols ####
addbinexe (uni_generate uni/generate.cc
  uni/livelock.cc uni/unifile.cc
  pfmla-glu.c pfmla.c pfmla.cc)
set_property (TARGET uni_generate
  APPEND PROPERTY INCLUDE_DIRECTORIES ${GluIncludePath})
target_link_libraries (uni_generate cu glu cal ${M_LIB})
set_target_properties (uni_generate PROPERTIES
  OUTPUT_NAME generate
  RUNTIME_OUTPUT_DIRECTORY ${UniringBinPath})

#### Translate between Unidirectional Ring Protocol Representations ####
addbinexe (uni_xlate uni/xlate.cc
  uni/livelock.cc uni/unifile.cc)
set_target_properties (uni_xlate PROPERTIES
  OUTPUT_NAME xlate
  RUNTIME_OUTPUT_DIRECTORY ${UniringBinPath})

#### Classify Unidirectional Ring Protocols ####
addbinexe (uni_classify uni/classify.cc
  uni/livelock.cc uni/unifile.cc
  pfmla-glu.c pfmla.c pfmla.cc)
set_property (TARGET uni_classify
  APPEND PROPERTY INCLUDE_DIRECTORIES ${GluIncludePath})
target_link_libraries (uni_classify cu glu cal ${M_LIB})
set_target_properties (uni_classify PROPERTIES
  OUTPUT_NAME classify
  RUNTIME_OUTPUT_DIRECTORY ${UniringBinPath})

#### Unidirectional Ring Synthesis ####
addbinexe (uni_synthesize uni/synthesize.cc uni/unifile.cc ${ProtoconSources})
set_property (TARGET uni_synthesize
  APPEND PROPERTY INCLUDE_DIRECTORIES ${GluIncludePath})
#set_property (TARGET uni_synthesize
#  PROPERTY COMPILE_FLAGS "-Wextra -std=c++11")
#set_property (TARGET uni_synthesize
#  PROPERTY LINK_FLAGS "-Wextra -std=c++11")
#set_source_files_properties (${BldPath}/uni/synthesize.cc
#  PROPERTIES COMPILE_FLAGS "-Wextra -std=c++11")
target_link_libraries (uni_synthesize cu glu cal ${M_LIB})
set_target_properties (uni_synthesize PROPERTIES
  OUTPUT_NAME synthesize
  RUNTIME_OUTPUT_DIRECTORY ${UniringBinPath})

