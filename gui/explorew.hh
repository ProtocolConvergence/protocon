
#ifndef ExploreW_HH_
#define ExploreW_HH_

#include <QDialog>
#include <QString>

namespace Ui {
  class ExploreW;
}
class QListWidget;
class QListWidgetItem;
class QProcess;

class ExploreW : public QDialog
{
Q_OBJECT

public:
  ExploreW(QWidget *parent = 0);
  ~ExploreW();

private slots:
  void ready_read();
  void ready_read_stderr();
  void randomize_state();
  void random_step();
  void act_assign(QListWidgetItem* item);

public:
  void update_data();
  void explore(QString xfilename);
private:
  Ui::ExploreW* ui;
  QProcess* process;

  bool updating;
  QString qbuf;
  bool gobble_section;
  QListWidget* list_widget;
};

#endif

