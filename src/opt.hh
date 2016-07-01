
#ifndef OPT_HH_
#define OPT_HH_
#include "cx/synhax.hh"
#include "cx/alphatab.hh"
#include "cx/map.hh"
#include "cx/table.hh"
#include "stabilization.hh"
#include "xnspec.hh"

#include "namespace.hh"

class AddConvergenceOpt;
class ProtoconFileOpt;
class ProtoconParamOpt;
class ProtoconOpt;

class ProtoconParamOpt {
public:
  Map<String, Xn::NatMap> constant_map;
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
  ProtoconParamOpt instance_def;
  Table< ProtoconParamOpt > instances;
  String log_ofilename;
  String xfilepath;
  String ofilepath;
  bool use_espresso;
  Table< String > xfilepaths;
  String model_ofilepath;
  String graphviz_ofilepath;
  String udp_ofilepath;
  String conflicts_xfilepath;
  String conflicts_ofilepath;
  String stats_ofilepath;
  String argline;

  MinimizeConflictsOrder conflict_order;

  ProtoconOpt()
    : task(SearchTask)
    , nparallel( 1 )
    , use_espresso( false )
    , conflict_order( HiLoOrder )
  {}
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

END_NAMESPACE
#endif

