
#include "stabilization.hh"

#include "xnsys.hh"

/**
 * Check for weak convergence to the invariant.
 */
  bool
weak_convergence_ck(const Cx::PFmla& xn, const Cx::PFmla& invariant)
{
  Cx::PFmla span0( invariant );
  while (!span0.tautology_ck()) {
    const Cx::PFmla& span1 = invariant | xn.pre(span0);
    if (span1.equiv_ck(span0))  return false;
    span0 = span1;
  }
  return true;
}

  bool
shadow_ck(Cx::PFmla* ret_invariant,
          const Xn::Sys& sys,
          const Cx::PFmla& lo_xn, const Cx::PFmla& hi_xn,
          const Cx::PFmla* scc)
{
  if (!sys.shadow_puppet_synthesis_ck()) {
    if (ret_invariant)
      *ret_invariant = sys.invariant;
    return true;
  }

  const Xn::Net& topo = sys.topology;
  const Cx::PFmla& shadow_invariant = sys.invariant;
  const Cx::PFmla& shadow_protocol = sys.shadow_pfmla;
  const Cx::PFmla& shadow_self = sys.shadow_self;
  const Cx::PFmla& shadow_live = shadow_invariant & shadow_protocol;

  // There shouldn't be non-progress cycles.
  if ((lo_xn & shadow_self & shadow_protocol.pre()).cycle_ck(shadow_invariant)) {
    return false;
  }

  // Invariant states with no transitions to them.
  const Cx::PFmla& shadow_beg =
    shadow_invariant - shadow_protocol.img(shadow_invariant);
  // Invariant states with no transitions from them.
  const Cx::PFmla& shadow_end =
    shadow_invariant - shadow_protocol.pre(shadow_invariant);

  // Over-approximation of invariant.
  Cx::PFmla hi_invariant = shadow_invariant;
  // Over-approximation of protocol which does not change shadow variables.
  Cx::PFmla hi_self = hi_xn & shadow_self;
  // Over-approximation of protocol which does change shadow variables.
  Cx::PFmla hi_live = hi_xn & shadow_protocol;

  // Trim all states which cannot be in the invariant since we cannot
  // simulate the shadow protocol in those states given the current
  // over-approximated protocol.
  while (true)
  {
    hi_invariant = lo_xn.closure_within(hi_invariant);

    const Cx::PFmla old_invariant = hi_invariant;
    const Cx::PFmla& hi_img = hi_invariant.as_img();

    hi_self &= hi_invariant;
    hi_self &= hi_img;

    hi_live &= hi_invariant;
    hi_live &= hi_img;
    hi_live -= (shadow_live - topo.smooth_pure_puppet_img_vbls(hi_live)).pre();

    const Cx::PFmla& hi_beg = hi_invariant & shadow_beg;
    const Cx::PFmla& hi_end = hi_invariant & shadow_end;

    hi_invariant &= hi_self.img_reach(hi_beg | hi_live.img());
    hi_invariant &= hi_self.pre_reach(hi_end | hi_live.pre());

    //hi_invariant &= shadow_beg | hi_protocol.img(hi_invariant);
    //hi_invariant &= shadow_end | hi_protocol.pre(hi_invariant);

    if (old_invariant.equiv_ck(hi_invariant)) {
      break;
    }
  }

  if (!shadow_invariant.equiv_ck(topo.smooth_pure_puppet_vbls(hi_invariant))) {
    return false;
  }

  if (!(lo_xn & hi_invariant).subseteq_ck(hi_live | hi_self)) {
    return false;
  }

  const Cx::PFmla& lhs =
    topo.smooth_pure_puppet_vbls(shadow_live);
  const Cx::PFmla& rhs =
    topo.smooth_pure_puppet_vbls(hi_live);
#if 0
  Claim( lhs.equiv_ck(rhs) );
#else
  if (!lhs.equiv_ck(rhs)) {
#if 0
    if (!(lhs <= rhs)) {
      DBog0("shadow_protocol is bigger");
      sys.topology.oput_one_xn(std::cerr, lhs - rhs);
    }
    if (!(rhs <= lhs)) {
      DBog0("hi_protocol is bigger");
      sys.topology.oput_one_xn(std::cerr, rhs - lhs);
    }
#endif
    return false;
  }
#endif

  if (scc) {
    if (!scc->subseteq_ck(hi_invariant)) {
      return false;
    }
  }
  else {
    if (lo_xn.cycle_ck(shadow_invariant - hi_invariant)) {
      return false;
    }
  }

  Cx::PFmla legit_protocol = hi_xn & (shadow_protocol | shadow_self);
  legit_protocol &= shadow_invariant;
  legit_protocol &= shadow_invariant.as_img();

  hi_invariant = legit_protocol.pre_reach(hi_invariant);
  hi_invariant = lo_xn.closure_within(hi_invariant);

  if (sys.direct_invariant_ck()) {
    if (!hi_invariant.equiv_ck(shadow_invariant)) {
      return false;
    }
  }

  if (ret_invariant)
    *ret_invariant = hi_invariant;
  return true;
}

  bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const Cx::PFmla& lo_xn, const Cx::PFmla& hi_xn)
{
  of << "Checking for deadlocks...\n";
  of.flush();
  if (!(~sys.invariant).subseteq_ck(hi_xn.pre())) {
    of << "Deadlock found.\n";
    of.flush();
    return false;
  }
  of << "Finding SCCs...\n";
  of.flush();
  Cx::PFmla scc( false );
  lo_xn.cycle_ck(&scc);
  if (!scc.subseteq_ck(sys.invariant)) {
    of << "Livelock found.\n";
    of.flush();
    return false;
  }
  of << "Calculating invariant...\n";
  of.flush();
  Cx::PFmla hi_invariant( false );
  if (!shadow_ck(&hi_invariant, sys, lo_xn, hi_xn, &scc)) {
    of << "Invariant not valid, given the protocol and behavior.\n";
    of.flush();
    return false;
  }
  of << "Checking for deadlocks in new invariant...\n";
  of.flush();
  if (!(~hi_invariant).subseteq_ck(hi_xn.pre())) {
    of << "Deadlock found.\n";
    of.flush();
    return false;
  }
  of << "Checking for weak convergence...\n";
  of.flush();
  if (!weak_convergence_ck(hi_xn, hi_invariant)) {
    of << "Weak convergence does not hold...\n";
    of.flush();
    return false;
  }
#if 0
  const Xn::Net& topo = sys.topology;
  of << "Checking for cycles using SCC_Find...\n";
  of.flush();
  if (SCC_Find(&scc, lo_xn, ~hi_invariant)) {
    of << "Livelock found.\n";
    topo.oput_all_pf(of, scc);
    of.flush();
    return false;
  }
#endif
  return true;
}

  bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const vector<uint>& actions,
                 const vector<uint>& candidates)
{
  const Xn::Net& topo = sys.topology;
  Cx::PFmla lo_xn( false );
  Cx::PFmla hi_xn( false );
  of << "Building transition relation...\n";
  of.flush();
  for (uint i = 0; i < actions.size(); ++i) {
    lo_xn |= topo.action_pfmla(actions[i]);
  }
  for (uint i = 0; i < candidates.size(); ++i) {
    hi_xn |= topo.action_pfmla(candidates[i]);
  }
  hi_xn |= lo_xn;
  return stabilization_ck(of, sys, lo_xn, hi_xn);
}

  bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const vector<uint>& actions)
{
  const vector<uint> candidates;
  return stabilization_ck(of, sys, actions, candidates);
}

  bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys)
{
  return stabilization_ck(of, sys, sys.actions);
}

