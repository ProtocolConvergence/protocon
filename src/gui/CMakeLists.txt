
find_package(Qt5Widgets)

if (NOT Qt5Widgets_FOUND)
  return()
endif()

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set (gui_HEADERS "mainw.hh" "explorew.hh" "searchdialog.hh")
set (gui_FORMS "mainw.ui"  "explorew.ui" "searchdialog.ui")
set (gui_SOURCES "mainw.cc" "main.cc" "explorew.cc" "searchdialog.cc")

add_definitions(${Qt5Widgets_DEFINITIONS})
qt5_wrap_ui(gui_FORMS_HEADERS ${gui_FORMS})
qt5_wrap_cpp(gui_HEADERS_MOC ${gui_HEADERS})


add_executable(protocon-gui
  ${gui_SOURCES}
  ${gui_HEADERS_MOC}
  ${gui_FORMS_HEADERS})

set_property(TARGET protocon-gui APPEND_STRING PROPERTY
  COMPILE_FLAGS " ${Qt5Widgets_EXECUTABLE_COMPILE_FLAGS}")
set_property(TARGET protocon-gui APPEND_STRING PROPERTY
  INCLUDE_DIRECTORIES "${CMAKE_CURRENT_BINARY_DIR}" ${Qt5Widgets_INCLUDE_DIRS})

target_link_libraries(protocon-gui Qt5::Widgets)

set_target_properties(protocon-gui PROPERTIES
  RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/../..")

install (TARGETS protocon-gui DESTINATION bin)

