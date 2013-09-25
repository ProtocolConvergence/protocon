
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

bool
shadow_ck(Cx::PFmla* ret_invariant,
          const Xn::Sys& sys,
          const Cx::PFmla& lo_xn, const Cx::PFmla& hi_xn,
          const Cx::PFmla* scc);
bool
weak_convergence_ck(const Cx::PFmla& xn, const Cx::PFmla& invariant);

bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const Cx::PFmla& lo_xn, const Cx::PFmla& hi_xn);
bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const vector<uint>& actions, const vector<uint>& candidates);
bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const vector<uint>& actions);
bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys);
#endif

