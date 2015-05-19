
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
  process->setProcessChannelMode(QProcess::SeparateChannels);

  connect(this, SIGNAL(rejected()), this, SLOT(closing()));

  connect(ui->randomizeButton, SIGNAL(clicked()), this, SLOT(randomize_state()));
  connect(ui->stepImgButton, SIGNAL(clicked()), this, SLOT(random_img_step()));
  connect(ui->syncStepImgButton, SIGNAL(clicked()), this, SLOT(sync_img_step()));
  connect(ui->stepPreButton, SIGNAL(clicked()), this, SLOT(random_pre_step()));
  connect(ui->valueList, SIGNAL(itemChanged(QListWidgetItem*)), this, SLOT(vbl_assign(QListWidgetItem*)));
  connect(ui->imgList, SIGNAL(itemClicked(QListWidgetItem*)), this, SLOT(act_assign(QListWidgetItem*)));
  connect(ui->preList, SIGNAL(itemClicked(QListWidgetItem*)), this, SLOT(act_assign(QListWidgetItem*)));

  ui->invariantInfluenceGroup->setId(ui->invariantTrueBtn, 0);
  ui->invariantInfluenceGroup->setId(ui->invariantDisplayBtn, 1);
  ui->invariantInfluenceGroup->setId(ui->invariantFalseBtn, 2);
  ui->silentInfluenceGroup->setId(ui->silentTrueBtn, 0);
  ui->silentInfluenceGroup->setId(ui->silentDisplayBtn, 1);
  ui->silentInfluenceGroup->setId(ui->silentFalseBtn, 2);
  ui->cycleInfluenceGroup->setId(ui->cycleTrueBtn, 0);
  ui->cycleInfluenceGroup->setId(ui->cycleDisplayBtn, 1);
  ui->cycleInfluenceGroup->setId(ui->cycleFalseBtn, 2);
  connect(ui->invariantInfluenceGroup, SIGNAL(buttonClicked(int)), this, SLOT(invariant_influence_changed(int)));
  connect(ui->silentInfluenceGroup, SIGNAL(buttonClicked(int)), this, SLOT(silent_influence_changed(int)));
  connect(ui->cycleInfluenceGroup, SIGNAL(buttonClicked(int)), this, SLOT(cycle_influence_changed(int)));

  ui->cycleInfluenceLayout->hide();
  connect(ui->cycleFindButton, SIGNAL(clicked()), this, SLOT(cycle_find_clicked()));
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
            ui->invariantStateLabel->setCurrentIndex(0);
          }
          if (line == "invariant 0") {
            ui->invariantStateLabel->setCurrentIndex(2);
          }
          if (line == "silent 1") {
            ui->silentStateLabel->setCurrentIndex(0);
          }
          if (line == "silent 0") {
            ui->silentStateLabel->setCurrentIndex(2);
          }
          if (line == "cycle 1") {
            ui->cycleStateLabel->setCurrentIndex(0);
          }
          if (line == "cycle 0") {
            ui->cycleStateLabel->setCurrentIndex(2);
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
ExploreW::random_img_step()
{
  if (updating)  return;
  QString line( "step img " );
  line += ui->nstepsSpinBox->cleanText();
  line += '\n';
  process->write(line.toAscii());
  gobble_section = true;
  update_data();
}

  void
ExploreW::sync_img_step()
{
  if (updating)  return;
  QString line( "sstep " );
  line += ui->nstepsSpinBox->cleanText();
  line += '\n';
  process->write(line.toAscii());
  gobble_section = true;
  update_data();
}

  void
ExploreW::random_pre_step()
{
  if (updating)  return;
  QString line( "step pre " );
  line += ui->nstepsSpinBox->cleanText();
  line += '\n';
  process->write(line.toAscii());
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
ExploreW::cycle_find_clicked()
{
  ui->cycleInfluenceLayout->show();
  process->write("predicate cycle display\n");
  update_data();
}

  void
ExploreW::predicate_influence_changed(const char* name, int idx)
{
  QString line("predicate ");
  line += name;
  line += ' ';
  if      (idx == 0)  line += "true";
  else if (idx == 1)  line += "display";
  else if (idx == 2)  line += "false";
  line += '\n';
  process->write(line.toAscii());
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
  process->write("predicate invariant display\n");
  process->write("predicate silent display\n");
  update_data();
}

