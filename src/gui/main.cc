
#include <QApplication>

#include "mainw.hh"

int main(int argc, char *argv[])
{
  QApplication app(argc, argv);
  app.setCursorFlashTime(0);
  MainW win;

  if (argv[1])
    win.open_file(argv[1]);

  win.show();
  return app.exec();
}

