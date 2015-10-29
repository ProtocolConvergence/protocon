
#ifndef STABILIZATION_HH_
#define STABILIZATION_HH_
#include "cx/synhax.hh"
#include "cx/table.hh"

namespace Cx {
  class PFmla;
  class OFile;
}
namespace Xn {
  class Sys;
}
namespace X {
  class Fmlae;
}

class StabilizationOpt
{
public:
  uint max_nlayers;
  bool count_convergence_layers;
  bool synchronous;

  StabilizationOpt()
    : max_nlayers( 0 )
    , count_convergence_layers( false )
    , synchronous( false )
  {}
};

class StabilizationCkInfo
{
public:
  Cx::Table<uint> actions;
  bool livelock_exists;
  Cx::Table<uint> livelock_actions;
  uint nlayers;

  bool find_livelock_actions;

  StabilizationCkInfo()
    : livelock_exists(false)
    , nlayers(0)
    , find_livelock_actions(false)
  {}
};

bool
shadow_ck(Cx::PFmla* ret_invariant,
          const Xn::Sys& sys,
          const Cx::PFmla& lo_xn,
          const Cx::PFmla& hi_xn,
          const X::Fmlae& lo_xfmlae,
          const Cx::PFmla& lo_scc,
          const bool explain_failure = false);
bool
weak_convergence_ck(const Cx::PFmla& xn, const Cx::PFmla& invariant);
bool
weak_convergence_ck(uint* ret_nlayers, const Cx::PFmla& xn,
                    const Cx::PFmla& invariant,
                    const Cx::PFmla& assumed);
bool
weak_convergence_ck(uint* ret_nlayers, const Cx::PFmla& xn,
                    const Cx::PFmla& invariant);

bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 const Cx::PFmla& lo_xn,
                 const Cx::PFmla& hi_xn,
                 const X::Fmlae& lo_xfmlae,
                 StabilizationCkInfo* info = 0);
bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 const vector<uint>& actions,
                 const vector<uint>& candidates,
                 StabilizationCkInfo* info = 0);
bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 const vector<uint>& actions,
                 StabilizationCkInfo* info = 0);
bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 StabilizationCkInfo* info = 0);
#endif

