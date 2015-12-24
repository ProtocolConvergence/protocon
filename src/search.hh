
#ifndef SEARCH_HH_
#define SEARCH_HH_
#include "cx/synhax.hh"
#include "cx/alphatab.hh"
#include "cx/table.hh"

#include "namespace.hh"

class AddConvergenceOpt;
class ConflictFamily;
class PartialSynthesis;
class ProtoconFileOpt;
class ProtoconOpt;
class SynthesisCtx;

bool
AddStabilization(vector<uint>& ret_actions,
                 PartialSynthesis& base_inst,
                 const AddConvergenceOpt& opt);
bool
AddStabilization(Xn::Sys& sys, const AddConvergenceOpt& opt);
bool
try_order_synthesis(vector<uint>& ret_actions,
                    PartialSynthesis& tape);
bool
rank_actions (Table< Table<uint> >& act_layers,
              const Xn::Net& topo,
              const vector<uint>& candidates,
              const X::Fmla& xn,
              const P::Fmla& legit);
void
oput_conflicts (const ConflictFamily& conflicts, const String& ofilename);
void
oput_conflicts (const ConflictFamily& conflicts, String ofilename, uint pcidx);
bool
initialize_conflicts(ConflictFamily& conflicts,
                     Table< FlatSet<uint> >& flat_conflicts,
                     const ProtoconOpt& exec_opt,
                     const AddConvergenceOpt& global_opt,
                     bool do_output);
void
multi_verify_stabilization
 (uint i,
  SynthesisCtx& synctx,
  vector<uint>& ret_actions,
  bool& solution_found,
  const ProtoconFileOpt& infile_opt,
  const ProtoconOpt& exec_opt,
  AddConvergenceOpt& opt);
bool
stabilization_search(vector<uint>& ret_actions,
                     const ProtoconFileOpt& infile_opt,
                     const ProtoconOpt& exec_opt,
                     const AddConvergenceOpt& global_opt);

END_NAMESPACE
#endif

