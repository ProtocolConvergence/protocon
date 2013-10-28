
#ifndef SEARCH_HH_
#define SEARCH_HH_
#include "cx/synhax.hh"
#include "cx/alphatab.hh"
#include "cx/table.hh"

namespace Cx {
  class PFmla;
}
namespace Xn {
  class Net;
  class Sys;
}
class AddConvergenceOpt;
class PartialSynthesis;
class ProtoconFileOpt;
class ProtoconOpt;
class ConflictFamily;

bool
AddConvergence(vector<uint>& ret_actions,
               PartialSynthesis& base_inst,
               const AddConvergenceOpt& opt);
bool
AddConvergence(Xn::Sys& sys, const AddConvergenceOpt& opt);
bool
try_order_synthesis(vector<uint>& ret_actions,
                    PartialSynthesis& tape);
bool
rank_actions (Cx::Table< Cx::Table<uint> >& act_layers,
              const Xn::Net& topo,
              const vector<uint>& candidates,
              const Cx::PFmla& xn,
              const Cx::PFmla& legit);
void
oput_conflicts (const ConflictFamily& conflicts, const Cx::String& ofilename);
void
oput_conflicts (const ConflictFamily& conflicts, Cx::String ofilename, uint pcidx);
bool
stabilization_search(vector<uint>& ret_actions,
                     const ProtoconFileOpt& infile_opt,
                     const ProtoconOpt& exec_opt,
                     const AddConvergenceOpt& global_opt);

#endif

