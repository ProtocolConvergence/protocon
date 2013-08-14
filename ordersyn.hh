
#ifndef ORDERSYN_HH_
#define ORDERSYN_HH_
#include "cx/synhax.hh"

namespace Xn {
  class ActSymm;
  class Sys;
}
class AddConvergenceOpt;

bool
flat_backtrack_synthesis(vector<uint>& ret_actions, const char* infile_path,
                         const AddConvergenceOpt& global_opt);
bool
ordering_synthesis(vector<uint>& ret_actions, const char* infile_path);

#endif

