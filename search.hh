
#ifndef ORDERSYN_HH_
#define ORDERSYN_HH_
#include "cx/synhax.hh"
#include "cx/alphatab.hh"
#include "cx/table.hh"

namespace Xn {
  class ActSymm;
  class Sys;
}
class AddConvergenceOpt;
class PartialSynthesis;
class ProtoconFileOpt;

class ProtoconOpt {
public:
  enum ExecTask {
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
AddConvergence(vector<uint>& ret_actions,
               const Xn::Sys& sys,
               PartialSynthesis& base_inst,
               const AddConvergenceOpt& opt);
bool
AddConvergence(Xn::Sys& sys, const AddConvergenceOpt& opt);
bool
stabilization_search(vector<uint>& ret_actions,
                     const ProtoconFileOpt& infile_opt,
                     const ProtoconOpt& exec_opt,
                     const AddConvergenceOpt& global_opt);

#endif

