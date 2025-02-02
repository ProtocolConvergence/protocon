FetchContent_Declare(
  Fildesh
  URL "https://github.com/fildesh/fildesh/releases/download/v0.2.0/fildesh-0.2.0.tar.gz"
  URL_HASH "SHA256=9a66f9622c558966091b4c8abc3b0ca2c0e6f17ace9c1c3720e83173ffddd569"
)
FetchContent_MakeAvailable(Fildesh)

set(Fildesh_INCLUDE_DIRS ${Fildesh_INCLUDE_DIRS} PARENT_SCOPE)
set(Fildesh_LIBRARIES ${Fildesh_LIBRARIES} PARENT_SCOPE)
set(FildeshSxproto_LIBRARIES ${FildeshSxproto_LIBRARIES} PARENT_SCOPE)
set(FildeshTool_cembed_EXECUTABLE ${FildeshTool_cembed_EXECUTABLE} PARENT_SCOPE)
set(FildeshTool_cswitch_EXECUTABLE ${FildeshTool_cswitch_EXECUTABLE} PARENT_SCOPE)
