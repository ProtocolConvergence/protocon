
#ifndef STABILIZATION_HH_
#define STABILIZATION_HH_
#include "cx/synhax.hh"

namespace Cx {
  class PFmla;
  class OFile;
}
namespace Xn {
  class Sys;
}

class StabilizationCkInfo
{
public:
  vector<uint> actions;
  bool livelock_exists;
  vector<uint> livelock_actions;

  StabilizationCkInfo()
    : livelock_exists(false)
  {}
};

bool
shadow_ck(Cx::PFmla* ret_invariant,
          const Xn::Sys& sys,
          const Cx::PFmla& lo_xn, const Cx::PFmla& hi_xn,
          const Cx::PFmla* lo_scc);
bool
weak_convergence_ck(const Cx::PFmla& xn, const Cx::PFmla& invariant);

bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const Cx::PFmla& lo_xn,
                 const Cx::PFmla& hi_xn,
                 StabilizationCkInfo* info = 0);
bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const vector<uint>& actions,
                 const vector<uint>& candidates,
                 StabilizationCkInfo* info = 0);
bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const vector<uint>& actions,
                 StabilizationCkInfo* info = 0);
bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 StabilizationCkInfo* info = 0);
#endif

