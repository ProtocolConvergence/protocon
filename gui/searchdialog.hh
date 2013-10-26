
#ifndef SearchDialog_HH_
#define SearchDialog_HH_

#include <QDialog>
namespace Ui {
  class SearchDialog;
}

//! [0]
class SearchDialog : public QDialog
{
Q_OBJECT

public:
  SearchDialog(QWidget *parent = 0);
  ~SearchDialog();

private slots:

private:
  Ui::SearchDialog* ui;
};
//! [0]

#endif
