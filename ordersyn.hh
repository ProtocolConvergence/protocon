
#ifndef ORDERSYN_HH_
#define ORDERSYN_HH_
#include "cx/synhax.hh"

namespace Xn {
  class ActSymm;
  class Sys;
}
class AddConvergenceOpt;
class ProtoconFileOpt;

bool
flat_backtrack_synthesis(vector<uint>& ret_actions,
                         const ProtoconFileOpt& infile_opt,
                         const AddConvergenceOpt& global_opt);

#endif

