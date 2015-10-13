
#ifndef OPT_HH_
#define OPT_HH_
#include "cx/synhax.hh"
#include "cx/alphatab.hh"
#include "cx/map.hh"
#include "cx/table.hh"
#include "stabilization.hh"
#include "xnspec.hh"

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
    SearchTask,
    TestTask,
    VerifyTask,
    MinimizeConflictsTask,
    InteractiveTask,
    NoTask,
    NExecTasks
  };
  enum MinimizeConflictsOrder {
    LoHiOrder,
    HiLoOrder,
    RandomOrder
  };

  ExecTask task;
  uint nparallel;
  Cx::Table< ProtoconParamOpt > params;
  Cx::String log_ofilename;
  Cx::String xfilepath;
  Cx::String ofilepath;
  bool use_espresso;
  Cx::Table< Cx::String > xfilepaths;
  Cx::String model_ofilepath;
  Cx::String graphviz_ofilepath;
  Cx::String udp_ofilepath;
  Cx::String conflicts_xfilepath;
  Cx::String conflicts_ofilepath;
  Cx::String stats_ofilepath;
  Cx::String argline;

  MinimizeConflictsOrder conflict_order;

  ProtoconOpt()
    : task(SearchTask)
    , nparallel( 1 )
    , params( 1 )
    , use_espresso( false )
    , conflict_order( HiLoOrder )
  {}
};

class ProtoconParamOpt {
public:
  Cx::Map<Cx::String, Xn::NatMap> constant_map;
  bool conflict;
  bool partial;
  StabilizationOpt stabilization_opt;

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

