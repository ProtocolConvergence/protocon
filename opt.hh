
#ifndef OPT_HH_
#define OPT_HH_
#include "cx/synhax.hh"
#include "cx/alphatab.hh"
#include "cx/map.hh"
#include "cx/table.hh"

namespace Xn {
  class Sys;
}
class AddConvergenceOpt;
class ProtoconFileOpt;
class ProtoconParamOpt;
class ProtoconOpt;

class ProtoconParamOpt {
public:
  Cx::Map<Cx::String, uint> constant_map;
  bool conflict;
  bool partial;
  ProtoconParamOpt()
    : conflict( true )
    , partial( true )
  {}
  bool conflict_ck() const {
    return conflict && partial;
  }
  bool partial_ck() const {
    return partial;
  }
};

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
  Cx::Table< ProtoconParamOpt > params;
  const char* log_ofilename;

  ProtoconOpt()
    : task(SearchTask)
    , params( 1 )
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

