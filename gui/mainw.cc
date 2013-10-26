
#include "mainw.hh"
#include "ui_mainw.h"
#include "searchdialog.hh"

#include <QFileDialog>
#include <QTextStream>

MainW::MainW(QWidget *parent)
    : QMainWindow(parent)
    , ui( new Ui::MainW )
    , search_dialog( new SearchDialog(this) )
{
  ui->setupUi(this);
  connect(ui->actionOpen, SIGNAL(triggered()), this, SLOT(open()));
  connect(ui->actionSave, SIGNAL(triggered()), this, SLOT(save()));
  connect(ui->actionSaveAs, SIGNAL(triggered()), this, SLOT(saveas()));
  connect(ui->actionQuit, SIGNAL(triggered()), qApp, SLOT(quit()));

  connect(ui->searchButton, SIGNAL(clicked()), this, SLOT(search()));
}

MainW::~MainW()
{
  delete ui;
  delete search_dialog;
}

/**
 * Open a new file.
 */
  void
MainW::open()
{
  QString fname = QFileDialog::getOpenFileName
    (this, tr("Open File"), "", tr("Files (*.*)"));
  
  filename = fname;
  QFile f(fname);
  if (!f.open(QFile::ReadOnly | QFile::Text))
    return;

  QTextStream in(&f);
  ui->textEdit->setText(in.readAll());
}

/**
 * Save the file.
 */
  void
MainW::save()
{
  if (this->filename.isEmpty()) {
    this->saveas();
    return;
  }

  QFile f(this->filename);
  if (!f.open(QFile::WriteOnly | QFile::Text))
    return;

  QTextStream out(&f);
  out << ui->textEdit->toPlainText();
}

/**
 * Save the file.
 */
  void
MainW::saveas()
{
  QString fname = QFileDialog::getSaveFileName
    (this, tr("Save File"), this->filename, tr("Files (*.*)"));

  if (this->filename.isEmpty()) {
    this->filename = fname;
  }
  QFile f(fname);

  QTextStream out(&f);
  out << ui->textEdit->toPlainText();
}

  void
MainW::search()
{
  search_dialog->show();
}

