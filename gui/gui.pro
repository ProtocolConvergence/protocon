
CONFIG += qt warn_on release

HEADERS = \
  mainw.hh \
  explorew.hh \
  searchdialog.hh
FORMS = \
  mainw.ui \
  explorew.ui \
  searchdialog.ui
SOURCES = \
  mainw.cc \
  main.cc \
  explorew.cc \
  searchdialog.cc

target.path = ./
sources.files = $$SOURCES $$HEADERS $$RESOURCES $$FORMS *.pro
sources.path = ./
INSTALLS += target sources

