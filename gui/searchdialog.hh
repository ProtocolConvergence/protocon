
#ifndef SearchDialog_HH_
#define SearchDialog_HH_

#include <QDialog>
namespace Ui {
  class SearchDialog;
}
class QProcess;

class SearchDialog : public QDialog
{
Q_OBJECT

public:
  SearchDialog(QWidget *parent = 0);
  ~SearchDialog();

  void search(QString xfilename, QString ofilename);

private slots:
  void append_output();
  void process_finished();

private:
  Ui::SearchDialog* ui;
  QProcess* process;
};

#endif
