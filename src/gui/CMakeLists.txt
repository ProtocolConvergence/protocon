
find_package (Qt5Widgets)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

if (Qt5Widgets_FOUND)
  set (USING_Qt5 TRUE)
  include_directories(${Qt5Widgets_INCLUDE_DIRS})
  add_definitions(${Qt5Widgets_DEFINITIONS})
  set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${Qt5Widgets_EXECUTABLE_COMPILE_FLAGS}")
else ()
  find_package(Qt4 COMPONENTS QTCORE QTGUI)
  if (NOT QT4_FOUND)
    return()
  endif ()
  include (${QT_USE_FILE})
  add_definitions (${QT_DEFINITIONS})
endif ()


set (gui_HEADERS mainw.hh explorew.hh searchdialog.hh)
set (gui_FORMS mainw.ui  explorew.ui searchdialog.ui)
set (gui_SOURCES mainw.cc main.cc explorew.cc searchdialog.cc)

if (USING_Qt5)
  qt5_wrap_ui (gui_FORMS_HEADERS ${gui_FORMS})
  qt5_wrap_cpp (gui_HEADERS_MOC ${gui_HEADERS})
else ()
  qt4_wrap_ui (gui_FORMS_HEADERS ${gui_FORMS})
  qt4_wrap_cpp (gui_HEADERS_MOC ${gui_HEADERS})
endif ()

include_directories (${CMAKE_CURRENT_BINARY_DIR})

add_executable (protocon-gui
  ${gui_SOURCES}
  ${gui_HEADERS_MOC}
  ${gui_FORMS_HEADERS})

if (USING_Qt5)
  target_link_libraries (protocon-gui Qt5::Widgets)
else ()
  target_link_libraries (protocon-gui ${QT_LIBRARIES})
endif ()

install (TARGETS protocon-gui DESTINATION bin)

