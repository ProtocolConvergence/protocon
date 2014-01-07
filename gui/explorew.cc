
#include "explorew.hh"
#include "ui_explorew.h"

#include <QDir>
#include <QProcess>

ExploreW::ExploreW(QWidget *parent)
    : QDialog(parent)
    , ui( new Ui::ExploreW )
    , process( new QProcess )
    , updating(false)
    , gobble_section(false)
{
  ui->setupUi(this);
  connect(process, SIGNAL(readyReadStandardOutput()), this, SLOT(ready_read()));
  connect(process, SIGNAL(readyReadStandardError()), this, SLOT(ready_read_stderr()));

  connect(ui->randomizeButton, SIGNAL(clicked()), this, SLOT(randomize_state()));
  connect(ui->stepButton, SIGNAL(clicked()), this, SLOT(random_step()));
  connect(ui->imgList, SIGNAL(itemActivated(QListWidgetItem*)), this, SLOT(act_assign(QListWidgetItem*)));
  connect(ui->preList, SIGNAL(itemActivated(QListWidgetItem*)), this, SLOT(act_assign(QListWidgetItem*)));

  process->setProcessChannelMode(QProcess::SeparateChannels);
}

ExploreW::~ExploreW()
{
  delete ui;
  delete process;
}

  void
ExploreW::ready_read()
{
  if (qbuf.isNull()) {
    qbuf = "";
  }
  qbuf.append(process->readAllStandardOutput());
  while (!qbuf.isEmpty())
  {
    int idx = -1;
    if (qbuf[0] == QChar('\n')) {
      idx = 0;
    }
    else {
      idx = qbuf.indexOf("\n\n");
    }
    if (idx < 0) {
      break;
    }
    QString lines(qbuf.left(idx));
    if (idx == 0)
      qbuf.remove(0, 1);
    else
      qbuf.remove(0, idx+2);

    if (gobble_section) {
      gobble_section = false;
    }
    else if (list_widget) {
      list_widget->clear();
      list_widget->addItems(lines.split("\n"));

      if (list_widget == ui->valueList) {
        list_widget = ui->imgList;
      }
      else if (list_widget == ui->imgList) {
        list_widget = ui->preList;
      }
      else if (list_widget == ui->preList) {
        list_widget = 0;
        qbuf.clear();
        updating = false;
        break;
      }
    }
  }
}

  void
ExploreW::ready_read_stderr()
{
  process->readAllStandardError();
}

  void
ExploreW::randomize_state()
{
  if (updating)  return;
  process->write("randomize\n");
  update_data();
}

  void
ExploreW::random_step()
{
  if (updating)  return;
  process->write("step\n");
  gobble_section = true;
  update_data();
}

  void
ExploreW::act_assign(QListWidgetItem* item)
{
  if (updating)  return;
  process->write(("assign " + item->text() + "\n").toAscii());
  update_data();
}

  void
ExploreW::update_data()
{
  process->write("show-state\nshow-img\nshow-pre\n");
  list_widget = ui->valueList;
  updating = true;
}

  void
ExploreW::explore(QString xfilename)
{
  QString exepath =
    QDir(QCoreApplication::applicationDirPath())
    .absoluteFilePath("protocon");
  QStringList args;
  args.push_back("-interactive");
  args.push_back("-x");
  args.push_back(xfilename);
  process->start(exepath, args, QProcess::ReadWrite);
  update_data();
}

