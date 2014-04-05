
#include "searchdialog.hh"
#include "ui_searchdialog.h"

#include <QDir>
#include <QScrollBar>
#include <QProcess>

SearchDialog::SearchDialog(QWidget *parent)
    : QDialog(parent)
    , ui( new Ui::SearchDialog )
    , process( new QProcess )
{
  ui->setupUi(this);

  process->setProcessChannelMode(QProcess::MergedChannels);

  connect(ui->killButton, SIGNAL(clicked()), process, SLOT(kill()));
  connect(ui->terminateButton, SIGNAL(clicked()), process, SLOT(terminate()));
  connect(ui->closeButton, SIGNAL(clicked()), this, SLOT(hide()));
  connect(ui->closeButton, SIGNAL(clicked()), ui->textEdit, SLOT(clear()));

  connect(process, SIGNAL(readyRead()), this, SLOT(append_output()));
  connect(process, SIGNAL(finished(int,QProcess::ExitStatus)), this, SLOT(process_finished()));

  ui->killButton->setEnabled(false);
  ui->terminateButton->setEnabled(false);
}

SearchDialog::~SearchDialog()
{
  delete ui;
  delete process;
}

  void
SearchDialog::search(QString xfilename, QString ofilename)
{
  ui->killButton->setEnabled(true);
  ui->terminateButton->setEnabled(true);
  ui->terminateButton->setDefault(true);
  ui->closeButton->setEnabled(false);

  ui->textEdit->clear();

  QString exepath =
    QDir(QCoreApplication::applicationDirPath())
    .absoluteFilePath("protocon");
  QStringList args;
  args.push_back("-serial");
  args.push_back("-x");
  args.push_back(xfilename);
  if (!ofilename.isEmpty()) {
    args.push_back("-o");
    args.push_back(ofilename);
  }
  process->start(exepath, args, QProcess::ReadOnly);
}

  void
SearchDialog::verify(QString xfilename)
{
  ui->killButton->setEnabled(true);
  ui->terminateButton->setEnabled(true);
  ui->terminateButton->setDefault(true);
  ui->closeButton->setEnabled(false);

  ui->textEdit->clear();

  QString exepath =
    QDir(QCoreApplication::applicationDirPath())
    .absoluteFilePath("protocon");
  QStringList args;
  args.push_back("-verify");
  args.push_back("-x");
  args.push_back(xfilename);
  process->start(exepath, args, QProcess::ReadOnly);
}

  void
SearchDialog::append_output()
{
  QScrollBar* vscroll = ui->textEdit->verticalScrollBar();
  bool do_scroll =
    !vscroll->isVisible() || vscroll->sliderPosition() == vscroll->maximum();

  QTextCursor c = ui->textEdit->textCursor();
  c.beginEditBlock();
  c.movePosition(QTextCursor::End);
  c.insertText(process->readAll());
  c.endEditBlock();

  if (do_scroll) {
    vscroll->setSliderPosition(vscroll->maximum());
  }
}

  void
SearchDialog::process_finished()
{
  ui->killButton->setEnabled(false);
  ui->terminateButton->setEnabled(false);
  ui->closeButton->setEnabled(true);
  ui->closeButton->setDefault(true);
}

