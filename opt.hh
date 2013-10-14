
#ifndef OPT_HH_
#define OPT_HH_
#include "cx/synhax.hh"
#include "cx/alphatab.hh"
#include "cx/table.hh"

namespace Xn {
  class Sys;
}
class AddConvergenceOpt;
class ProtoconFileOpt;
class ProtoconOpt;

class ProtoconOpt {
public:
  enum ExecTask {
    TestTask,
    SearchTask,
    VerifyTask,
    MinimizeConflictsTask,
    NExecTasks
  };

  ExecTask task;
  Cx::Table< std::pair<Cx::String, uint> > params;
  const char* log_ofilename;

  ProtoconOpt()
    : task(SearchTask)
    , log_ofilename(0)
  {}
};

  bool
protocon_options
  (Xn::Sys& sys,
   int argi,
   int argc,
   char** argv,
   AddConvergenceOpt& opt,
   const char*& modelFilePath,
   ProtoconFileOpt& infile_opt,
   const char*& outfile_path,
   ProtoconOpt& exec_opt);

#endif

