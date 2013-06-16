
#ifndef ORDERSYN_HH_
#define ORDERSYN_HH_
#include "cx/synhax.hh"

namespace Xn {
  class ActSymm;
  class Sys;
}

bool
candidate_actions(vector<uint>& candidates, const Xn::Sys& sys);
bool
coexist_ck(const Xn::ActSymm& a, const Xn::ActSymm& b);
bool
ordering_synthesis(vector<uint>& ret_actions, const char* infile_path);

#endif

