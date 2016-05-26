
#ifndef STABILIZATION_HH_
#define STABILIZATION_HH_
#include "cx/synhax.hh"
#include "cx/table.hh"

#include "namespace.hh"

class StabilizationOpt
{
public:
  uint max_nlayers;
  bool count_convergence_layers;
  bool count_convergence_steps;
  bool synchronous;
  bool uniring;

  StabilizationOpt()
    : max_nlayers( 0 )
    , count_convergence_layers( true )
    , count_convergence_steps( true )
    , synchronous( false )
    , uniring( false )
  {}
};

class StabilizationCkInfo
{
public:
  Table<uint> actions;
  bool livelock_exists;
  Table<uint> livelock_actions;
  uint nlayers;

  bool find_livelock_actions;

  StabilizationCkInfo()
    : livelock_exists(false)
    , nlayers(0)
    , find_livelock_actions(false)
  {}
};

bool
shadow_ck(P::Fmla* ret_invariant,
          const Xn::Sys& sys,
          const X::Fmla& lo_xn,
          const X::Fmla& hi_xn,
          const X::Fmlae& lo_xfmlae,
          const P::Fmla& lo_scc,
          const bool explain_failure = false);
bool
weak_convergence_ck(const X::Fmla& xn, const P::Fmla& invariant);
bool
weak_convergence_ck(uint* ret_nlayers, const X::Fmla& xn,
                    const P::Fmla& invariant,
                    const P::Fmla& assumed);
bool
weak_convergence_ck(uint* ret_nlayers, const X::Fmla& xn,
                    const P::Fmla& invariant);

bool
stabilization_ck(OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 const X::Fmla& lo_xn,
                 const X::Fmla& hi_xn,
                 const X::Fmlae& lo_xfmlae,
                 StabilizationCkInfo* info = 0);
bool
stabilization_ck(OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 const vector<uint>& actions,
                 const vector<uint>& candidates,
                 StabilizationCkInfo* info = 0);
bool
stabilization_ck(OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 const vector<uint>& actions,
                 StabilizationCkInfo* info = 0);
bool
stabilization_ck(OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 StabilizationCkInfo* info = 0);

END_NAMESPACE
#endif

