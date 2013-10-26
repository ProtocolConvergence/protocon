
#include "searchdialog.hh"
#include "ui_searchdialog.h"

SearchDialog::SearchDialog(QWidget *parent)
    : QDialog(parent)
    , ui( new Ui::SearchDialog )
{
  ui->setupUi(this);

  connect(ui->closeButton, SIGNAL(clicked()), this, SLOT(hide()));
  ui->killButton->setEnabled(false);
  ui->terminateButton->setEnabled(false);
  //ui->closeButton->setEnabled(false);
}

SearchDialog::~SearchDialog()
{
  delete ui;
}

#if 0
  void
SearchDialog::swag()
{
  QCoreApplication::applicationDirPath()
  QProcess ( const QStringList & args, QObject * parent = 0, const char * name = 0 ) 
}
#endif

