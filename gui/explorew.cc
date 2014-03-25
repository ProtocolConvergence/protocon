
#include <iostream>
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

  connect(this, SIGNAL(rejected()), this, SLOT(closing()));

  connect(ui->randomizeButton, SIGNAL(clicked()), this, SLOT(randomize_state()));
  connect(ui->stepButton, SIGNAL(clicked()), this, SLOT(random_step()));
  connect(ui->valueList, SIGNAL(itemChanged(QListWidgetItem*)), this, SLOT(vbl_assign(QListWidgetItem*)));
  connect(ui->imgList, SIGNAL(itemActivated(QListWidgetItem*)), this, SLOT(act_assign(QListWidgetItem*)));
  connect(ui->preList, SIGNAL(itemActivated(QListWidgetItem*)), this, SLOT(act_assign(QListWidgetItem*)));
  connect(ui->invariantCheckBox, SIGNAL(clicked(bool)), this, SLOT(invariant_clicked(bool)));
  connect(ui->deadlockCheckBox, SIGNAL(clicked(bool)), this, SLOT(deadlock_clicked(bool)));
  connect(ui->livelockCheckBox, SIGNAL(clicked(bool)), this, SLOT(livelock_clicked(bool)));
  ui->invariantLabel->hide();
  ui->deadlockLabel->hide();
  ui->livelockLabel->hide();

  process->setProcessChannelMode(QProcess::SeparateChannels);
}

ExploreW::~ExploreW()
{
  delete ui;
  delete process;
}

  void
ExploreW::closing()
{
  process->write("exit\n");
  process->closeWriteChannel();
  process->waitForFinished();
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
    else if (!command_queue.empty()) {
      CommandId command = command_queue.front();
      command_queue.pop_front();

      if (command == ShowState) {
        ui->valueList->clear();
        ui->valueList->addItems(lines.split("\n"));
        vbl_names.clear();
        for (uint i = 0; i < (uint)ui->valueList->count(); i++) {
          QListWidgetItem* item = ui->valueList->item(i);
          item->setFlags(item->flags() | Qt::ItemIsEditable);
          vbl_names.push_back(item->text().section("==", 0, 0));
        }
      }
      else if (command == ShowImg) {
        ui->imgList->clear();
        ui->imgList->addItems(lines.split("\n"));
      }
      else if (command == ShowPre) {
        ui->preList->clear();
        ui->preList->addItems(lines.split("\n"));
      }
      else if (command == ShowSat) {
        QStringList sats = lines.split("\n");
        while (!sats.empty()) {
          QString line = sats.front();
          sats.pop_front();
          if (line == "invariant 1") {
            ui->invariantLabel->hide();
          }
          if (line == "invariant 0") {
            ui->invariantLabel->show();
          }
          if (line == "deadlock 1") {
            ui->deadlockLabel->hide();
          }
          if (line == "deadlock 0") {
            ui->deadlockLabel->show();
          }
          if (line == "scc 1") {
            ui->livelockLabel->hide();
          }
          if (line == "scc 0") {
            ui->livelockLabel->show();
          }
        }
      }

      if (command_queue.empty()) {
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
ExploreW::vbl_assign(QListWidgetItem* item)
{
  if (updating)  return;
  QString text = item->text();
  text.remove(QRegExp(".*=="));
  int row = ui->valueList->row(item);
  process->write(("assign " + vbl_names[row] + ":=" + text + "\n").toAscii());
  //std::cerr << ("assign " + vbl_names[row] + ":=" + text + "\n").toStdString();
  update_data();
}

  void
ExploreW::invariant_clicked(bool checked)
{
  QString line("conj-invariant ");
  line += checked ? "1" : "0";
  line += '\n';
  process->write(line.toAscii());
  if (!checked)
    ui->invariantLabel->hide();
  update_data();
}

  void
ExploreW::deadlock_clicked(bool checked)
{
  QString line("conj-deadlock ");
  line += checked ? "1" : "0";
  line += '\n';
  process->write(line.toAscii());
  if (!checked)
    ui->deadlockLabel->hide();
  update_data();
}

  void
ExploreW::livelock_clicked(bool checked)
{
  QString line("conj-scc ");
  line += checked ? "1" : "0";
  line += '\n';
  process->write(line.toAscii());
  if (!checked)
    ui->livelockLabel->hide();
  update_data();
}

  void
ExploreW::update_data()
{
  process->write("show-state\nshow-img\nshow-pre\nshow-sat\n");
  this->command_queue << ShowState << ShowImg << ShowPre << ShowSat;
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

