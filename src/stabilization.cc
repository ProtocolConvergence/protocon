
#include "stabilization.hh"

#include "xnsys.hh"

#include "namespace.hh"

/**
 * Check for weak convergence to the invariant.
 */
  bool
weak_convergence_ck(const X::Fmla& xn, const P::Fmla& invariant)
{
#if 1
  return xn.pre_reach(invariant).tautology_ck();
#else
  P::Fmla span0( invariant );
  while (!span0.tautology_ck()) {
    const P::Fmla& span1 = invariant | xn.pre(span0);
    if (span1.equiv_ck(span0))  return false;
    span0 = span1;
  }
  return true;
#endif
}

  bool
weak_convergence_ck(uint* ret_nlayers, const X::Fmla& xn, const P::Fmla& invariant, const P::Fmla& assumed)
{
  uint nlayers = 1;
  P::Fmla span0(assumed - invariant);

  while (true) {
    const P::Fmla& span1 = span0 - xn.pre(assumed - span0);
    if (span0.equiv_ck(span1))  break;
    span0 = span1;

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
  return !span0.sat_ck();
}

  bool
weak_convergence_ck(uint* ret_nlayers, const X::Fmla& xn, const P::Fmla& invariant)
{
  return weak_convergence_ck(ret_nlayers, xn, invariant, P::Fmla(true));
}


  bool
shadow_ck(P::Fmla* ret_invariant,
          const Xn::Sys& sys,
          const X::Fmla& lo_xn,
          const X::Fmla& hi_xn,
          const X::Fmlae& lo_xfmlae,
          const P::Fmla& lo_scc,
          const bool explain_failure)
{
  const Xn::Net& topo = sys.topology;
  const Xn::InvariantStyle invariant_style = sys.spec->invariant_style;
  const Xn::InvariantScope invariant_scope = sys.spec->invariant_scope;
  const Xn::InvariantBehav invariant_behav = sys.spec->invariant_behav;
  const P::Fmla& shadow_invariant = sys.invariant & sys.closed_assume;

  if (invariant_behav == Xn::FutureSilent) {
    if (lo_scc.sat_ck()) {
      if (explain_failure)
        DBog0( "Protocol is not silent." );
      return false;
    }
  }

  if (!sys.shadow_puppet_synthesis_ck() &&
      invariant_scope != Xn::FutureInvariant)
  {
    // Closure.
    if (!lo_xn.img(shadow_invariant).subseteq_ck(shadow_invariant)) {
      return false;
    }
    // Shadow behavior.
    if (invariant_style != Xn::FutureAndClosed) {
      if (!(sys.shadow_pfmla & shadow_invariant).subseteq_ck(hi_xn)) {
        return false;
      }
      if (!(lo_xn & shadow_invariant).subseteq_ck(sys.shadow_pfmla)) {
        return false;
      }
    }
    // Specification said this should be an active protocol.
    if (invariant_behav == Xn::FutureActiveShadow ||
        invariant_style == Xn::FutureAndActiveShadow)
    {
      if (!shadow_invariant.subseteq_ck(hi_xn.pre())) {
        if (explain_failure)
          DBog0( "Deadlock in invariant." );
        return false;
      }
    }

    if (ret_invariant)
      *ret_invariant = shadow_invariant;
    return true;
  }

  const X::Fmla& shadow_self =
    shadow_invariant & topo.proj_shadow(topo.identity_xn);
  const X::Fmla& shadow_live =
    shadow_invariant & topo.proj_shadow(sys.shadow_pfmla);

  // There shouldn't be non-progress cycles.
  if (topo.probabilistic_ck()) {
    if (lo_xfmlae.probabilistic_livelock_ck(0, shadow_invariant, shadow_live, &lo_xn)) {
      if (explain_failure)
        DBog0( "Non-progress cycle in invariant." );
      return false;
    }
  }
  else if ((lo_xn & shadow_self).cycle_ck(lo_scc & shadow_live.pre())) {
    if (explain_failure)
      DBog0( "Non-progress cycle in invariant." );
    return false;
  }

  // Invariant states with no transitions to them.
  const P::Fmla& shadow_beg =
    shadow_invariant - shadow_live.img();
  // Invariant states with no transitions from them.
  const P::Fmla& shadow_end =
    shadow_invariant - shadow_live.pre();

  // Over-approximation of protocol which does not change shadow variables.
  X::Fmla hi_self = hi_xn & shadow_self;
  // Over-approximation of protocol which does change shadow variables.
  X::Fmla hi_live = hi_xn & shadow_live;

  if (invariant_style == Xn::FutureAndSilent) {
    hi_live = false;
    hi_self = false;
  }
  if (invariant_style == Xn::FutureAndActiveShadow) {
    hi_self = false;
  }

  // Over-approximation of invariant.
  P::Fmla hi_invariant =
    shadow_invariant - (lo_xn - (hi_live | hi_self)).pre();

  // Trim all states which cannot be in the invariant since we cannot
  // simulate the shadow protocol in those states given the current
  // over-approximated protocol.
  while (true)
  {
    hi_invariant = lo_xn.closure_within(hi_invariant);
    const P::Fmla old_invariant = hi_invariant;

    hi_live &= hi_invariant;
    hi_live &= hi_invariant.as_img();

    hi_self &= hi_invariant;
    hi_self &= hi_invariant.as_img();

    hi_invariant &= hi_self.img_reach(shadow_beg | hi_live.img());
    hi_invariant &= hi_self.pre_reach(shadow_end | hi_live.pre());

    if (old_invariant.equiv_ck(hi_invariant)) {
      break;
    }
  }

  Claim( (lo_xn & hi_invariant).subseteq_ck(hi_live | hi_self) );

  if (invariant_scope == Xn::FutureInvariant) {
    // Over-approximated protocol must preserve some part of the invariant.
    if (!hi_invariant.sat_ck()) {
      if (explain_failure) {
        DBog0( "Does not preserve any invariant." );
      }
      return false;
    }
  }
  // Over-approximated protocol must preserve shadow invariant.
  else if (!topo.proj_shadow(shadow_invariant).equiv_ck(topo.proj_shadow(hi_invariant))) {
    if (explain_failure) {
      DBog0( "Does not preserve shadow invariant." );
      P::Fmla pf = topo.proj_shadow(shadow_invariant) - topo.proj_shadow(hi_invariant);
      X::Fmla xn = pf & lo_xn & (~topo.proj_shadow(hi_invariant)).as_img();
      topo.oput_vbl_names(DBogOF);
      topo.oput_one_xn(DBogOF, xn);
      // May not output anything.
    }
    return false;
  }

  if (invariant_scope == Xn::FutureInvariant) {
    // Over-approximated protocol must preserve some shadow transitions.
    // Actually, this should come for free.
  }
  // Over-approximated protocol must preserve shadow transitions.
  else if (!topo.proj_shadow(shadow_live).equiv_ck(topo.proj_shadow(hi_live))) {
    if (explain_failure)
      DBog0( "Does not preserve shadow transitions." );
    return false;
  }

  // Under-approximated protocol must not have a cycle outside of the new invariant.
  if (topo.probabilistic_ck()) {
    if (lo_xfmlae.probabilistic_livelock_ck(0, lo_scc - hi_invariant, X::Fmla(false), &lo_xn)) {
      if (explain_failure)
        DBog0( "Cycle outside invariant." );
      return false;
    }
  }
  else if (!lo_scc.subseteq_ck(hi_invariant)) {
    if (explain_failure)
      DBog0( "Cycle outside invariant." );
    return false;
  }

  if (invariant_behav == Xn::FutureActiveShadow) {
    // Every transition in the SCC must change shadow variables.
    if (lo_scc.overlap_ck(lo_xn & shadow_self)) {
      if (explain_failure)
        DBog0( "A shadow self-loop may be taken infinitely often." );
      return false;
    }
    X::Fmla hi_scc_xn = hi_live - (lo_xn & shadow_self).pre();
#if 1
    P::Fmla hi_scc(false);
    if (!hi_scc_xn.cycle_ck(&hi_scc, hi_invariant)) {
      if (explain_failure)
        DBog0( "No active shadow in over-approximation." );
      return false;
    }
#else
    // Not an SCC, but the cycle check can be expensive.
    P::Fmla hi_scc = hi_scc_xn.pre();
#endif
    if (!weak_convergence_ck(0, hi_xn, hi_scc, hi_invariant)) {
      if (explain_failure) {
        DBog0( "Not all executions are infinite ones that eventually" );
        DBog0( "`-> change shadow variables at every transition." );
      }
      return false;
    }
  }

  if (invariant_style == Xn::FutureAndShadow) {
    hi_invariant = (hi_xn & (shadow_self | shadow_live)).pre_reach(hi_invariant);
    hi_invariant = lo_xn.closure_within(hi_invariant);
  }
  if (invariant_style == Xn::FutureAndActiveShadow) {
    hi_invariant = (hi_xn & shadow_live).pre_reach(hi_invariant);
    hi_invariant = lo_xn.closure_within(hi_invariant);
  }

  if (invariant_scope == Xn::DirectInvariant) {
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
stabilization_ck(OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 const X::Fmla& lo_xn,
                 const X::Fmla& hi_xn,
                 const X::Fmlae& lo_xfmlae,
                 StabilizationCkInfo* info)
{
  const Xn::Net& topo = sys.topology;
  const bool show_failure = true;

  if (!sys.invariant.overlap_ck(sys.closed_assume)) {
    if (!sys.invariant.sat_ck())
      of << "Invariant is empty." << of.endl();
    else if (!sys.closed_assume.sat_ck())
      of << "Assumed states are empty." << of.endl();
    else
      of << "No overlap between invariant and assumed states." << of.endl();
    return false;
  }

  of << "Checking for self-loops...\n";
  if (topo.probabilistic_ck()) {
  }
  else if (sys.closed_assume.overlap_ck(lo_xn & topo.identity_xn)) {
    of << "Self-loop found.\n";
    if (show_failure) {
      const X::Fmla& puppet_self = sys.closed_assume & lo_xn & topo.identity_xn;
      P::Fmla pf = (lo_xn.img() & puppet_self.pre()).pick_pre();
      topo.oput_vbl_names(of);
      topo.oput_one_pf(of, lo_xn.pre(pf));
      topo.oput_one_pf(of, pf);
      topo.oput_one_pf(of, puppet_self.img(pf));
    }
    of.flush();
    return false;
  }

  of << "Checking for closure...\n";
  if (!sys.closed_assume.tautology_ck()) {
    P::Fmla pf = lo_xn.img(sys.closed_assume) - sys.closed_assume;
    if (pf.sat_ck()) {
      of << "Assumed states are not closed.\n";
      if (show_failure) {
        pf = pf.pick_pre();
        topo.oput_vbl_names(of);
        topo.oput_one_pf(of, lo_xn.pre(pf) & sys.closed_assume);
        topo.oput_one_pf(of, pf);
      }
      of.flush();
      return false;
    }
  }

  of << "Checking for deadlocks..." << of.endl();
  if (!(~sys.invariant & sys.closed_assume).subseteq_ck(hi_xn.pre())) {
    of << "Deadlock found.\n";
    if (show_failure) {
      P::Fmla pf = (~sys.invariant & sys.closed_assume) - hi_xn.pre();
      topo.oput_vbl_names(of);
      topo.oput_one_pf(of, pf);
    }
    of.flush();
    return false;
  }
  of << "Finding cycles..." << of.endl();
  P::Fmla scc( false );
  uint nlayers = opt.max_nlayers;
  if (topo.probabilistic_ck()) {
    nlayers = 1;
    P::Fmla tmp_invariant = lo_xn.closure_within(sys.invariant & sys.closed_assume);
    lo_xfmlae.probabilistic_livelock_ck(&scc, sys.closed_assume, (~tmp_invariant).cross(tmp_invariant), &lo_xn);
  }
  else if (opt.uniring) {
    lo_xfmlae.uniring_cycle_ck(&scc, &nlayers,
                               (opt.count_convergence_layers ? &sys.invariant : 0),
                               &sys.closed_assume);
  }
  else {
    lo_xn.cycle_ck(&scc, &nlayers,
                   (opt.count_convergence_layers ? &sys.invariant : 0),
                   &sys.closed_assume);
  }
  if (info)  info->nlayers = nlayers;
  if (opt.max_nlayers > 0 && nlayers > opt.max_nlayers) {
    of << "Too many layers to "
      << (opt.count_convergence_layers ? "converge" : "fixpoint")
      << "." << of.endl();
    return false;
  }

  if (!scc.subseteq_ck(sys.invariant)) {
    of << "Livelock found.\n";
    if (info) {
      info->livelock_exists = true;
      if (info->find_livelock_actions) {
        Table<P::Fmla> states;
        info->livelock_actions = info->actions;
        if (!topo.probabilistic_ck()) {
          find_livelock_actions(info->livelock_actions, lo_xn, scc, sys.invariant, topo);
        }
        of << info->livelock_actions.size() << " actions involved in livelocks.\n";
      }
    }
    if (show_failure) {
      topo.oput_vbl_names(of);
      //oput_one_cycle(of, lo_xn, scc, scc - sys.invariant, topo);
      //topo.oput_all_pf(of, scc - sys.invariant);
      topo.oput_one_pf(of, scc - sys.invariant);
    }
    of.flush();
    return false;
  }
  of << "Checking behavior within the invariant..." << of.endl();
  P::Fmla hi_invariant( false );
  if (!shadow_ck(&hi_invariant, sys, lo_xn, hi_xn, lo_xfmlae, scc, true)) {
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

  uint reach_nlayers = 0;
  // Only check for weak convergence if it isn't implied.
  if (!lo_xn.equiv_ck(hi_xn)) {
    of << "Checking for weak convergence...\n";
    of.flush();
    if (!weak_convergence_ck(&reach_nlayers, hi_xn, hi_invariant, sys.closed_assume)) {
      of << "Weak convergence does not hold...\n";
      of.flush();
      return false;
    }
  }
  else if (opt.uniring) {
    const P::Fmla& invariant =
      (opt.count_convergence_layers ? hi_invariant : (~lo_xn.pre() | scc));
    lo_xfmlae.uniring_weak_convergence_ck(&reach_nlayers, invariant, sys.closed_assume);
  }
  else if (!opt.synchronous) {
    const P::Fmla& invariant =
      (opt.count_convergence_layers ? hi_invariant : (~lo_xn.pre() | scc));
    weak_convergence_ck(&reach_nlayers, lo_xn, invariant, sys.closed_assume);
  }
  else {
    reach_nlayers = nlayers;
  }
  if (opt.count_convergence_steps) {
    nlayers -= 1;
    reach_nlayers -= 1;
  }
  of << "Max strong/weak " << (opt.synchronous ? "sync" : "async") << " "
    << (opt.count_convergence_steps ? "steps" : "layers") << " to "
    << (opt.count_convergence_layers ? "converge" : "fixpoint")
    << ": " << nlayers << "/" << reach_nlayers << of.endl();
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
stabilization_ck(OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 const vector<uint>& actions,
                 const vector<uint>& candidates,
                 StabilizationCkInfo* info)
{
  const Xn::Net& topo = sys.topology;
  of << "Building transition relation...\n";
  of.flush();

  if (opt.synchronous) {
    Table<uint> sync_actions( actions );
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
    Claim( !topo.probabilistic_ck() );
    X::Fmlae lo_xfmlae;
    return stabilization_ck(of, sys, opt, lo_xn, hi_xn, lo_xfmlae, info);
  }

  X::Fmlae lo_xn( &topo.xfmlae_ctx );
  for (uint i = 0; i < actions.size(); ++i) {
    if (!topo.lightweight) {
      lo_xn |= topo.action_xfmlae(actions[i]);
    }
    else {
      const Table<uint>& rep_actions = topo.represented_actions[actions[i]];
      for (uint j = 0; j < rep_actions.sz(); ++j) {
        X::Fmlae act_xn;
        topo.make_action_xfmlae(&act_xn, rep_actions[j]);
        lo_xn |= act_xn;
      }
    }
  }

  X::Fmlae hi_xn( lo_xn );
  for (uint i = 0; i < candidates.size(); ++i) {
    if (!topo.lightweight) {
      hi_xn |= topo.action_xfmlae(candidates[i]);
    }
    else {
      const Table<uint>& rep_candidates = topo.represented_actions[candidates[i]];
      for (uint j = 0; j < rep_candidates.sz(); ++j) {
        X::Fmlae act_xn;
        topo.make_action_xfmlae(&act_xn, rep_candidates[j]);
        hi_xn |= act_xn;
      }
    }
  }

  if (info) {
    info->actions = actions;
  }
  return stabilization_ck(of, sys, opt, lo_xn.xfmla(), hi_xn.xfmla(), lo_xn, info);
}

  bool
stabilization_ck(OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 const vector<uint>& actions,
                 StabilizationCkInfo* info)
{
  const vector<uint> candidates;
  return stabilization_ck(of, sys, opt, actions, candidates, info);
}

  bool
stabilization_ck(OFile& of, const Xn::Sys& sys,
                 const StabilizationOpt& opt,
                 StabilizationCkInfo* info)
{
  if (opt.synchronous) {
    return stabilization_ck(of, sys, opt, sys.actions, info);
  }
  if (!info || sys.topology.lightweight) {
    const Xn::Net& topo = sys.topology;
    X::Fmlae xn(&topo.xfmlae_ctx);
    for (uint i = 0; i < topo.pcs.sz(); ++i) {
      const Xn::Pc& pc = topo.pcs[i];
      xn[i] = pc.puppet_xn;
    }
    return stabilization_ck(of, sys, opt, sys.direct_pfmla,
                            sys.direct_pfmla, xn, info);
  }
  return stabilization_ck(of, sys, opt, sys.actions, info);
}

}
