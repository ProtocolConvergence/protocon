
#ifndef MainW_HH_
#define MainW_HH_

#include <QMainWindow>
namespace Ui {
  class MainW;
}
class SearchDialog;

class MainW : public QMainWindow
{
Q_OBJECT

public:
  MainW(QWidget *parent = 0);
  ~MainW();

  bool open_file(QString fname);

private slots:
  void open();
  void new_file();
  bool save();
  bool saveas();
  void search();

private:
  QString filename;
  Ui::MainW* ui;
  SearchDialog* search_dialog;
};

#endif
