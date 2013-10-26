
#include <QApplication>

#include "mainw.hh"

int main(int argc, char *argv[])
{
  QApplication app(argc, argv);
  MainW win;
  win.show();
  return app.exec();
}

