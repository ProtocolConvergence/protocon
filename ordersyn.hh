
#ifndef ORDERSYN_HH_
#define ORDERSYN_HH_
#include "cx/synhax.hh"

namespace Xn {
  class ActSymm;
  class Sys;
}
class AddConvergenceOpt;
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
  const char* log_ofilename;

  ProtoconOpt()
    : task(SearchTask)
    , log_ofilename(0)
  {}
};

bool
flat_backtrack_synthesis(vector<uint>& ret_actions,
                         const ProtoconFileOpt& infile_opt,
                         const ProtoconOpt& exec_opt,
                         const AddConvergenceOpt& global_opt);

#endif

