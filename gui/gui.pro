
CONFIG += qt warn_on release

HEADERS = \
  mainw.hh \
  searchdialog.hh
FORMS = \
  mainw.ui \
  searchdialog.ui
SOURCES = \
  mainw.cc \
  main.cc \
  searchdialog.cc

target.path = ./
sources.files = $$SOURCES $$HEADERS $$RESOURCES $$FORMS *.pro
sources.path = ./
INSTALLS += target sources

