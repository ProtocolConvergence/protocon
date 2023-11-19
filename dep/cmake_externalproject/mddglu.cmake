ExternalProject_Add(mdd_glu_project
  GIT_REPOSITORY "https://github.com/ProtocolConvergence/mdd-glu.git"
  GIT_TAG "b0068976e7a6b4d2c18178d37c4038f8c0900bce"
  CMAKE_ARGS "-DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>"
)
add_library(mdd_cu_lib STATIC IMPORTED)
add_library(mdd_glu_lib STATIC IMPORTED)
ExternalProject_Get_Property(mdd_glu_project INSTALL_DIR)
set_target_properties(mdd_cu_lib PROPERTIES IMPORTED_LOCATION "${INSTALL_DIR}/lib/libcu.a")
set_target_properties(mdd_glu_lib PROPERTIES IMPORTED_LOCATION "${INSTALL_DIR}/lib/libglu.a")
add_dependencies(mdd_cu_lib mdd_glu_project)
add_dependencies(mdd_glu_lib mdd_glu_project)
list(APPEND mdd_glu_libs mdd_cu_lib mdd_glu_lib)
set(GluIncludePath "${INSTALL_DIR}/include")
