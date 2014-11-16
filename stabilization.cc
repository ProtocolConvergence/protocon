
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
weak_convergence_ck(uint* ret_nlayers, const Cx::PFmla& xn, const Cx::PFmla& invariant, const Cx::PFmla& assumed)
{
  uint nlayers = 1;
  Cx::PFmla visit( invariant );
  Cx::PFmla layer( xn.pre(invariant) - visit );
  while (layer.sat_ck()) {
    visit |= layer;
    layer = (xn.pre(layer) - visit) & assumed;
    if (ret_nlayers) {
      nlayers += 1;
      if (*ret_nlayers > 0 && nlayers > *ret_nlayers) {
        *ret_nlayers = nlayers;
        return false;
      }
    }
  }
  if (ret_nlayers)
    *ret_nlayers = nlayers;
  return assumed.subseteq_ck(visit);
}

  bool
weak_convergence_ck(uint* ret_nlayers, const Cx::PFmla& xn, const Cx::PFmla& invariant)
{
  return weak_convergence_ck(ret_nlayers, xn, invariant, Cx::PFmla(true));
}

  bool
shadow_ck(Cx::PFmla* ret_invariant,
          const Xn::Sys& sys,
          const Cx::PFmla& lo_xn, const Cx::PFmla& hi_xn,
          const Cx::PFmla* lo_scc)
{
  static const bool explain_failure = false;
  const Xn::Net& topo = sys.topology;
  const Cx::PFmla& shadow_invariant = sys.invariant & sys.closed_assume;

  if (!sys.shadow_puppet_synthesis_ck()) {
    // Closure.
    if (!lo_xn.img(shadow_invariant).subseteq_ck(shadow_invariant)) {
      return false;
    }
    // Shadow behavior.
    if (!(sys.shadow_pfmla & shadow_invariant).subseteq_ck(hi_xn)) {
      return false;
    }
    if (!(lo_xn & shadow_invariant).subseteq_ck(sys.shadow_pfmla)) {
      return false;
    }
    if (ret_invariant)
      *ret_invariant = shadow_invariant;
    return true;
  }

  const Cx::PFmla& shadow_self =
    shadow_invariant & topo.proj_shadow(topo.identity_xn);
  const Cx::PFmla& shadow_live =
    shadow_invariant & topo.proj_shadow(sys.shadow_pfmla);

  // There shouldn't be non-progress cycles.
  if (lo_scc) {
    if ((lo_xn & shadow_self).cycle_ck(*lo_scc & shadow_live.pre())) {
      if (explain_failure)
        DBog0( "Non-progress cycle in invariant." );
      return false;
    }
  }
  else {
    if ((lo_xn & shadow_self).cycle_ck(shadow_live.pre())) {
      if (explain_failure)
        DBog0( "Non-progress cycle in invariant." );
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

  if (sys.spec->invariant_behav == Xn::FutureSilent) {
    hi_invariant -= lo_xn.pre();
  }

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
  if (!topo.proj_shadow(shadow_invariant).equiv_ck(topo.proj_shadow(hi_invariant))) {
      if (explain_failure)
        DBog0( "Does not preserve shadow invariant." );
    return false;
  }

  // Over-approximated protocol must preserve shadow transitions.
  if (!shadow_live.equiv_ck(topo.proj_shadow(hi_live))) {
      if (explain_failure)
        DBog0( "Does not preserve shadow transitions." );
    return false;
  }

  // Over-approximated protocol must preserve shadow transitions.
  if (lo_scc) {
    if (!lo_scc->subseteq_ck(hi_invariant)) {
      if (explain_failure)
        DBog0( "Cycle outside invariant." );
      return false;
    }
  }
  else {
    if (lo_xn.cycle_ck(shadow_invariant - hi_invariant)) {
      if (explain_failure)
        DBog0( "Cycle outside invariant." );
      return false;
    }
  }

  hi_invariant = (hi_xn & (shadow_self | shadow_live)).pre_reach(hi_invariant);
  hi_invariant = lo_xn.closure_within(hi_invariant);

  if (sys.direct_invariant_ck()) {
    if (!hi_invariant.equiv_ck(shadow_invariant)) {
      if (explain_failure)
        DBog0( "Closure violated." );
      return false;
    }
  }

  if (ret_invariant)
    *ret_invariant = hi_invariant;
  return true;
}

  bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 const Cx::PFmla& lo_xn,
                 const Cx::PFmla& hi_xn,
                 StabilizationCkInfo* info)
{
  const Xn::Net& topo = sys.topology;
  const bool show_failure = true;
  if (sys.shadow_puppet_synthesis_ck()) {
    of << "Checking for bad shadow...\n";
  }
  else {
    of << "Checking for self-loops...\n";
  }
  if ((lo_xn.img() & sys.closed_assume).overlap_ck(lo_xn & topo.proj_puppet(topo.identity_xn))) {
    if (sys.shadow_puppet_synthesis_ck()) {
      of << "Pure shadow behavior is not put together properly.\n";
    }
    else {
      of << "Self-loop found.\n";
    }
    if (show_failure) {
      const Cx::PFmla& puppet_self = lo_xn & topo.proj_puppet(topo.identity_xn);
      Cx::PFmla pf = (lo_xn.img() & puppet_self.pre()).pick_pre();
      topo.oput_vbl_names(of);
      topo.oput_one_pf(of, lo_xn.pre(pf));
      topo.oput_one_pf(of, pf);
      topo.oput_one_pf(of, puppet_self.img(pf));
    }
    of.flush();
    return false;
  }

  of << "Checking for deadlocks..." << of.endl();
  if (!(~sys.invariant & sys.closed_assume).subseteq_ck(hi_xn.pre())) {
    of << "Deadlock found.\n";
    if (show_failure) {
      Cx::PFmla pf = (~sys.invariant & sys.closed_assume) - hi_xn.pre();
      topo.oput_vbl_names(of);
      topo.oput_one_pf(of, pf);
    }
    of.flush();
    return false;
  }
  of << "Finding cycles..." << of.endl();
  Cx::PFmla scc( false );
  uint nlayers = opt.max_nlayers;
  lo_xn.cycle_ck(&scc, &nlayers,
                 (opt.count_convergence_layers ? &sys.invariant : 0),
                 &sys.closed_assume);
  if (info)  info->nlayers = nlayers;
  if (opt.max_nlayers > 0 && nlayers > opt.max_nlayers) {
    of << "Too many layers to "
      << (opt.count_convergence_layers ? "converge" : "fixpoint")
      << "." << of.endl();
    return false;
  }
  of << "Max " << (opt.synchronous ? "sync" : "async") << " layers to "
    << (opt.count_convergence_layers ? "converge" : "fixpoint")
    << ": " << nlayers << "\n";

  if (!scc.subseteq_ck(sys.invariant)) {
    of << "Livelock found.\n";
    if (info) {
      info->livelock_exists = true;
      if (info->find_livelock_actions) {
        Cx::Table<Cx::PFmla> states;
        info->livelock_actions = info->actions;
        find_livelock_actions(info->livelock_actions, lo_xn, scc, sys.invariant, topo);
        of << info->livelock_actions.size() << " actions involved in livelocks.\n";
      }
    }
    if (show_failure) {
      topo.oput_vbl_names(of);
      oput_one_cycle(of, lo_xn, scc, topo);
    }
    of.flush();
    return false;
  }
  of << "Checking behavior within the invariant..." << of.endl();
  Cx::PFmla hi_invariant( false );
  if (!shadow_ck(&hi_invariant, sys, lo_xn, hi_xn, &scc)) {
    of << "Invariant not valid, given the protocol and behavior.\n";
    of.flush();
    return false;
  }
  if (sys.shadow_puppet_synthesis_ck()) {
    of << "Checking for deadlocks in new invariant..." << of.endl();
  }
  if (!(~hi_invariant & sys.closed_assume).subseteq_ck(hi_xn.pre())) {
    of << "Deadlock found.\n";
    of.flush();
    return false;
  }
  // Only check for weak convergence if it isn't implied.
  if (!lo_xn.equiv_ck(hi_xn)) {
    of << "Checking for weak convergence...\n";
    of.flush();
    if (!weak_convergence_ck(0, hi_xn, hi_invariant, sys.closed_assume)) {
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
                 const StabilizationOpt& opt,
                 const vector<uint>& actions,
                 const vector<uint>& candidates,
                 StabilizationCkInfo* info)
{
  const Xn::Net& topo = sys.topology;
  of << "Building transition relation...\n";
  of.flush();

  if (opt.synchronous) {
    Cx::Table<uint> sync_actions( actions );
    const X::Fmla lo_xn = sys.topology.sync_xn(sync_actions);

    for (uint i = 0; i < candidates.size(); ++i) {
      sync_actions << candidates[i];
    }

    const X::Fmla hi_xn =
      (candidates.empty()
       ? lo_xn
       : sys.topology.sync_xn(sync_actions));

    if (!candidates.empty()) {
      DBog0( "Synchronous semantics don't work well with overapproximation." );
      DBog0( "Expect failure." );
    }

    if (info) {
      info->actions = actions;
    }
    return stabilization_ck(of, sys, opt, lo_xn, hi_xn, info);
  }

  X::Fmla lo_xn( false );
  X::Fmla lo_pure_shadow_pf( true );
  for (uint i = 0; i < actions.size(); ++i) {
    if (!topo.lightweight) {
      lo_xn |= topo.action_pfmla(actions[i]);
      lo_pure_shadow_pf &= topo.pure_shadow_pfmla(actions[i]);
    }
    else {
      const Cx::Table<uint>& rep_actions = topo.represented_actions[actions[i]];
      for (uint j = 0; j < rep_actions.sz(); ++j) {
        X::Fmla act_xn;
        X::Fmla pure_shadow_act_xn;
        topo.make_action_pfmla(&act_xn, &pure_shadow_act_xn, rep_actions[j]);
        lo_xn |= act_xn;
        lo_pure_shadow_pf &= pure_shadow_act_xn;
      }
    }
    //Claim( lo_pure_shadow_pf.sat_ck() );
  }

  Cx::PFmla hi_xn( lo_xn );
  Cx::PFmla hi_pure_shadow_pf( lo_pure_shadow_pf );
  for (uint i = 0; i < candidates.size(); ++i) {
    if (!topo.lightweight) {
      hi_xn |= topo.action_pfmla(candidates[i]);
    }
    else {
      const Cx::Table<uint>& rep_candidates = topo.represented_actions[candidates[i]];
      for (uint j = 0; j < rep_candidates.sz(); ++j) {
        X::Fmla act_xn;
        topo.make_action_pfmla(&act_xn, 0, rep_candidates[j]);
        hi_xn |= act_xn;
      }
    }
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
  return stabilization_ck(of, sys, opt, lo_xn, hi_xn, info);
}

  bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 const vector<uint>& actions,
                 StabilizationCkInfo* info)
{
  const vector<uint> candidates;
  return stabilization_ck(of, sys, opt, actions, candidates, info);
}

  bool
stabilization_ck(Cx::OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 StabilizationCkInfo* info)
{
  if (opt.synchronous) {
    return stabilization_ck(of, sys, opt, sys.actions, info);
  }
  if (!info || sys.topology.lightweight) {
    return stabilization_ck(of, sys, opt, sys.direct_pfmla, sys.direct_pfmla, info);
  }
  return stabilization_ck(of, sys, opt, sys.actions, info);
}

