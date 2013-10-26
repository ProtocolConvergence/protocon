
#ifndef MainW_HH_
#define MainW_HH_

#include <QMainWindow>
namespace Ui {
  class MainW;
}
class SearchDialog;

//! [0]
class MainW : public QMainWindow
{
Q_OBJECT

public:
  MainW(QWidget *parent = 0);
  ~MainW();

private slots:
  void open();
  void save();
  void saveas();
  void search();

private:
  QString filename;
  Ui::MainW* ui;
  SearchDialog* search_dialog;
};
//! [0]

#endif
