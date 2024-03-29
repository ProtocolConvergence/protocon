
#include "src/cx/synhax.hh"

#include "src/stabilization.hh"
#include "src/inst.hh"
#include "src/xnsys.hh"

#include "src/namespace.hh"

static void
TestShadowColorRing()
{
  std::ostream& of = std::cerr;
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;
  const uint npcs = 3;
  SilentShadowRing(sys, npcs, "x", 3, "c", 3);

  for (uint i = 0; i < npcs; ++i) {
    sys.invariant &=
      (topo.pfmla_vbl(*topo.vbl_symms[1].membs[i])
       !=
       topo.pfmla_vbl(*topo.vbl_symms[1].membs[umod_int(i+1, npcs)]));
  }

  static const uint act_vals[][4] = {
    // x[i-1] x[i] x[i+1] --> x[i]'
    { 0, 0, 0, 1 },
    { 0, 0, 1, 1 },
    { 0, 0, 2, 1 },
    { 0, 2, 0, 2 },
    { 0, 2, 1, 2 },
    { 0, 2, 2, 1 },
    { 1, 0, 0, 0 },
    { 1, 1, 0, 2 },
    { 1, 1, 1, 0 },
    { 1, 1, 2, 0 },
    { 1, 2, 1, 2 },
    { 1, 2, 2, 0 },
    { 2, 0, 0, 0 },
    { 2, 0, 1, 0 },
    { 2, 1, 0, 1 },
    { 2, 1, 1, 1 },
    { 2, 1, 2, 1 },
    { 2, 2, 0, 2 },
    { 2, 2, 1, 2 },
    { 2, 2, 2, 0 }
  };

  for (uint actidx = 0; actidx < topo.n_possible_acts; ++actidx)
  {
    Xn::ActSymm act_symm;
    topo.action(act_symm, actidx);

    bool add_action = false;
    for (uint i = 0; i < ArraySz(act_vals) && !add_action; ++i) {
      add_action =
        (   act_vals[i][0] == act_symm.guard(0)
         && (   act_vals[i][1] == act_symm.guard(1)
             || act_vals[i][3] == act_symm.guard(1))
         && act_vals[i][2] == act_symm.guard(2)
         && act_vals[i][3] == act_symm.assign(0)
         && act_vals[i][3] == act_symm.assign(1));
    }

    if (add_action)
    {
      uint rep_actidx = topo.representative_action_index(actidx);
      if (rep_actidx == actidx)
        sys.actions.push_back(actidx);
    }
  }

  StabilizationOpt stabilization_opt;
  const bool stabilizing =
    stabilization_ck(of, sys, stabilization_opt, sys.actions);
  assert(stabilizing);
}

END_NAMESPACE

int main() {
  using namespace PROTOCON_NAMESPACE;
  TestShadowColorRing();
  return 0;
}

