
find_package (Qt4)

if (NOT QT4_FOUND)
  return()
endif ()

include (${QT_USE_FILE})
add_definitions (${QT_DEFINITIONS})

set (gui_HEADERS mainw.hh explorew.hh searchdialog.hh)
set (gui_FORMS mainw.ui  explorew.ui searchdialog.ui)
set (gui_SOURCES mainw.cc main.cc explorew.cc searchdialog.cc)

QT4_WRAP_UI (gui_FORMS_HEADERS ${gui_FORMS})
QT4_WRAP_CPP (gui_HEADERS_MOC ${gui_HEADERS})

include_directories (${CMAKE_CURRENT_BINARY_DIR})

add_executable (protocon-gui
  ${gui_SOURCES}
  ${gui_HEADERS_MOC}
  ${gui_FORMS_HEADERS})
target_link_libraries (protocon-gui ${QT_LIBRARIES})

install (TARGETS protocon-gui DESTINATION bin)

