
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
class ProtoconOpt;
class ProtoconParamOpt;

class ProtoconOpt {
public:
  enum ExecTask {
    TestTask,
    SearchTask,
    VerifyTask,
    MinimizeConflictsHiLoTask,
    MinimizeConflictsLoHiTask,
    NExecTasks
  };

  ExecTask task;
  Cx::Table< ProtoconParamOpt > params;
  Cx::String log_ofilename;
  Cx::String ofilepath;
  Cx::Table< Cx::String > xfilepaths;
  Cx::String model_ofilepath;
  Cx::String conflicts_xfilepath;
  Cx::String conflicts_ofilepath;

  ProtoconOpt()
    : task(SearchTask)
    , params( 1 )
  {}
};

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


  bool
protocon_options
  (Xn::Sys& sys,
   int argi,
   int argc,
   char** argv,
   AddConvergenceOpt& opt,
   ProtoconFileOpt& infile_opt,
   ProtoconOpt& exec_opt);

#endif

