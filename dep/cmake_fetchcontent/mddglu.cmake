FetchContent_Declare(
  MddGlu
  GIT_REPOSITORY "https://github.com/ProtocolConvergence/mdd-glu.git"
  GIT_TAG "b47adfb9019f9e50230003cae520f5da96dabf2f"
)
FetchContent_MakeAvailable(MddGlu)

set(MddGlu_INCLUDE_DIRS "${MddGlu_INCLUDE_DIRS}" PARENT_SCOPE)
set(MddGlu_LIBRARIES "${MddGlu_LIBRARIES}" PARENT_SCOPE)
