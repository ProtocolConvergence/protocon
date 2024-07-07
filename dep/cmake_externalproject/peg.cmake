ExternalProject_Add(peg_project
  URL "https://github.com/gpakosz/peg/releases/download/0.1.18/peg-0.1.18.tar.gz"
  URL_HASH SHA256=d5031a3cce592ea6d002a4996be8165775fdabf4f393857dfe1601f02078a8ae
  BUILD_IN_SOURCE 1
  CONFIGURE_COMMAND echo "No configure step."
  INSTALL_COMMAND echo "No install step."
  )
add_executable(peg_leg IMPORTED)
ExternalProject_Get_Property(peg_project SOURCE_DIR)
set_target_properties(peg_leg PROPERTIES IMPORTED_LOCATION "${SOURCE_DIR}/leg")
add_dependencies (peg_leg peg_project)
