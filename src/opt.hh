
#ifndef OPT_HH_
#define OPT_HH_
#include <vector>

#include "cx/alphatab.hh"
#include "stabilization.hh"
#include "xnspec.hh"
#include "cx/map.hh"

#include "cx/synhax.hh"
#include "namespace.hh"

class AddConvergenceOpt;
class ProtoconFileOpt;
class ProtoconParamOpt;
class ProtoconOpt;

class ProtoconParamOpt {
public:
  Map<std::string, Xn::NatMap> constant_map;
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
  std::vector<ProtoconParamOpt> instances;
  std::string log_ofilename;
  std::string xfilepath;
  std::string ofilepath;
  bool use_espresso;
  std::vector<std::string> xfilepaths;
  std::string model_ofilepath;
  String graphviz_ofilepath;
  String udp_ofilepath;
  bool only_udp_include;
  std::string pla_ofilepath;
  String conflicts_xfilepath;
  String conflicts_ofilepath;
  String stats_ofilepath;
  String argline;

  MinimizeConflictsOrder conflict_order;

  ProtoconOpt()
    : task(SearchTask)
    , nparallel( 1 )
    , use_espresso( false )
    , only_udp_include( false )
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

