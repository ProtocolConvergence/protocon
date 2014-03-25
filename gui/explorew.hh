
#ifndef ExploreW_HH_
#define ExploreW_HH_

#include <QDialog>
#include <QString>
#include <QStringList>

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

  enum CommandId { ShowState, ShowImg, ShowPre, ShowSat };

private slots:
  void closing();
  void ready_read();
  void ready_read_stderr();
  void randomize_state();
  void random_step();
  void act_assign(QListWidgetItem* item);
  void vbl_assign(QListWidgetItem* item);
  void invariant_clicked(bool checked);
  void deadlock_clicked(bool checked);
  void livelock_clicked(bool checked);

public:
  void update_data();
  void explore(QString xfilename);
private:
  Ui::ExploreW* ui;
  QProcess* process;

  bool updating;
  QString qbuf;
  bool gobble_section;
  QStringList vbl_names;
  QList<CommandId> command_queue;
};

#endif

