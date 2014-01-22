
#include "stabilization.hh"

#include "xnsys.hh"

/**
 * Check for weak convergence to the invariant.
 */
  bool
weak_convergence_ck(const Cx::PFmla& xn, const Cx::PFmla& invariant)
{
#if 1
  return xn.pre_reach(invariant).tautology_ck();
#else
  Cx::PFmla span0( invariant );
  while (!span0.tautology_ck()) {
    const Cx::PFmla& span1 = invariant | xn.pre(span0);
    if (span1.equiv_ck(span0))  return false;
    span0 = span1;
  }
  return true;
#endif
}

  bool
shadow_ck(Cx::PFmla* ret_invariant,
          const Xn::Sys& sys,
          const Cx::PFmla& lo_xn, const Cx::PFmla& hi_xn,
          const Cx::PFmla* lo_scc)
{
  if (!sys.shadow_puppet_synthesis_ck()) {
    if (ret_invariant)
      *ret_invariant = sys.invariant;
    return true;
  }

  const Xn::Net& topo = sys.topology;
  const Cx::PFmla& shadow_invariant = sys.invariant;
  const Cx::PFmla& shadow_self =
    shadow_invariant & topo.proj_shadow(topo.identity_xn);
  const Cx::PFmla& shadow_live =
    shadow_invariant & topo.proj_shadow(sys.shadow_pfmla);

  // There shouldn't be non-progress cycles.
  if (lo_scc) {
    if ((lo_xn & shadow_self).cycle_ck(*lo_scc & shadow_live.pre())) {
      return false;
    }
  }
  else {
    if ((lo_xn & shadow_self).cycle_ck(shadow_live.pre())) {
      return false;
    }
  }

  // Invariant states with no transitions to them.
  const Cx::PFmla& shadow_beg =
    shadow_invariant - shadow_live.img();
  // Invariant states with no transitions from them.
  const Cx::PFmla& shadow_end =
    shadow_invariant - shadow_live.pre();

  // Over-approximation of invariant.
  Cx::PFmla hi_invariant = shadow_invariant;
  // Over-approximation of protocol which does not change shadow variables.
  Cx::PFmla hi_self = hi_xn & shadow_self;
  // Over-approximation of protocol which does change shadow variables.
  Cx::PFmla hi_live = hi_xn & shadow_live;

  // Trim all states which cannot be in the invariant since we cannot
  // simulate the shadow protocol in those states given the current
  // over-approximated protocol.
  while (true)
  {
    hi_invariant = lo_xn.closure_within(hi_invariant);
    const Cx::PFmla old_invariant = hi_invariant;

    hi_invariant -= (lo_xn - (hi_self | hi_live)).pre();
    const Cx::PFmla& hi_img = hi_invariant.as_img();

    hi_self &= hi_invariant;
    hi_self &= hi_img;

    hi_live &= hi_invariant;
    hi_live &= hi_img;
    hi_live -= (shadow_live - topo.proj_img_shadow(hi_live)).pre();

    hi_invariant &= hi_self.img_reach(shadow_beg | hi_live.img());
    hi_invariant &= hi_self.pre_reach(shadow_end | hi_live.pre());

    if (old_invariant.equiv_ck(hi_invariant)) {
      break;
    }
  }

  Claim( (lo_xn & hi_invariant).subseteq_ck(hi_live | hi_self) );

  // Over-approximated protocol must preserve shadow invariant.
  if (!shadow_invariant.equiv_ck(topo.proj_shadow(hi_invariant))) {
    return false;
  }

  // Over-approximated protocol must preserve shadow transitions.
  if (!shadow_live.equiv_ck(topo.proj_shadow(hi_live))) {
    return false;
  }

  // Over-approximated protocol must preserve shadow transitions.
  if (lo_scc) {
    if (!lo_scc->subseteq_ck(hi_invariant)) {
      return false;
    }
  }
  else {
    if (lo_xn.cycle_ck(shadow_invariant - hi_invariant)) {
      return false;
    }
  }

  hi_invariant = (hi_xn & (shadow_self | shadow_live)).pre_reach(hi_invariant);
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
                 const Cx::PFmla& lo_xn,
                 const Cx::PFmla& hi_xn,
                 StabilizationCkInfo* info)
{
  const Xn::Net& topo = sys.topology;
  of << "Checking for bad shadow...\n";
  if (lo_xn.img().overlap_ck(lo_xn & topo.proj_puppet(topo.identity_xn))) {
    of << "Pure shadow behavior is not put together properly.\n";
    if (false) {
      const Cx::PFmla& puppet_self = lo_xn & topo.proj_puppet(topo.identity_xn);
      Cx::PFmla pf = (lo_xn.img() & puppet_self.pre()).pick_pre();
      topo.oput_one_pf(of, lo_xn.pre(pf));
      topo.oput_one_pf(of, pf);
      topo.oput_one_pf(of, puppet_self.img(pf));
    }
    of.flush();
    return false;
  }

  of << "Checking for deadlocks...\n";
  of.flush();
  if (!(~sys.invariant).subseteq_ck(hi_xn.pre())) {
    of << "Deadlock found.\n";
    if (false) {
      topo.oput_all_pf(of, (~sys.invariant) - (hi_xn.pre()));
    }
    of.flush();
    return false;
  }
  of << "Finding SCCs...\n";
  of.flush();
  Cx::PFmla scc( false );
  lo_xn.cycle_ck(&scc);
  if (!scc.subseteq_ck(sys.invariant)) {
    of << "Livelock found.\n";
    if (info) {
      info->livelock_exists = true;
      Cx::Table<Cx::PFmla> states;
      info->livelock_actions = info->actions;
      find_one_cycle(info->livelock_actions, lo_xn, scc, topo);
      of << info->livelock_actions.size() << " actions involved in livelocks.\n";
    }
    if (false) {
      oput_one_cycle(of, lo_xn, scc, topo);
    }
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
  // Only check for weak convergence if it isn't implied.
  if (!lo_xn.equiv_ck(hi_xn)) {
    of << "Checking for weak convergence...\n";
    of.flush();
    if (!weak_convergence_ck(hi_xn, hi_invariant)) {
      of << "Weak convergence does not hold...\n";
      of.flush();
      return false;
    }
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
                 const vector<uint>& candidates,
                 StabilizationCkInfo* info)
{
  const Xn::Net& topo = sys.topology;
  Cx::PFmla lo_xn( false );
  Cx::PFmla lo_pure_shadow_pf( true );
  of << "Building transition relation...\n";
  of.flush();
  for (uint i = 0; i < actions.size(); ++i) {
    lo_xn |= topo.action_pfmla(actions[i]);
    lo_pure_shadow_pf &= topo.pure_shadow_pfmla(actions[i]);
    //Claim( lo_pure_shadow_pf.sat_ck() );
  }
  Cx::PFmla hi_xn( lo_xn );
  Cx::PFmla hi_pure_shadow_pf( lo_pure_shadow_pf );
  for (uint i = 0; i < candidates.size(); ++i) {
    hi_xn |= topo.action_pfmla(candidates[i]);
    // TODO
    //hi_pure_shadow_pf |= topo.pure_shadow_pfmla(candidates[i]);
  }
  lo_xn &= lo_pure_shadow_pf & lo_pure_shadow_pf.as_img();
  hi_xn &= hi_pure_shadow_pf & hi_pure_shadow_pf.as_img();
  const Cx::PFmla& puppet_self = topo.proj_puppet(topo.identity_xn);
  lo_xn |= puppet_self & ~lo_pure_shadow_pf & lo_pure_shadow_pf.as_img();
  hi_xn |= puppet_self & ~hi_pure_shadow_pf & hi_pure_shadow_pf.as_img();

  if (info) {
    info->actions = actions;
  }
  return stabilization_ck(of, sys, lo_xn, hi_xn, info);
}

  bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const vector<uint>& actions,
                 StabilizationCkInfo* info)
{
  const vector<uint> candidates;
  return stabilization_ck(of, sys, actions, candidates, info);
}

  bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 StabilizationCkInfo* info)
{
  if (info) {
    return stabilization_ck(of, sys, sys.actions, info);
  }
  else {
    return stabilization_ck(of, sys, sys.direct_pfmla, sys.direct_pfmla, info);
  }
}

