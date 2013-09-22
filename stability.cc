
#include "stability.hh"

  bool
candidate_actions(vector<uint>& candidates, const Xn::Sys& sys)
{
  const Xn::Net& topo = sys.topology;

  if (sys.invariant.tautology_ck(false)) {
    DBog0( "Invariant is empty!" );
    return false;
  }

  if (sys.invariant.tautology_ck(true)) {
    DBog0( "All states are invariant!" );
    if (!sys.shadow_puppet_synthesis_ck()) {
      return true;
    }
  }

  for (uint actidx = 0; actidx < topo.n_possible_acts; ++actidx) {
    bool add = true;

    Xn::ActSymm act;
    topo.action(act, actidx);
    const Xn::PcSymm& pc_symm = *act.pc_symm;
    const Cx::PFmla& act_pf = topo.action_pfmla(actidx);

    // Check for self-loops.
    if (add) {
      bool selfloop = true;
      for (uint j = 0; j < pc_symm.wvbl_symms.sz(); ++j) {
        if (act.assign(j) != act.aguard(j)) {
          selfloop = false;
        }
      }
      add = !selfloop;
      if (false && selfloop) {
        OPut((DBogOF << "Action " << actidx << " is a self-loop: "), act) << '\n';
      }
    }

    if (add && sys.direct_invariant_ck()) {
      if (!act_pf.img(sys.invariant).subseteq_ck(sys.invariant)) {
        add = false;
        if (false) {
          OPut((DBogOF << "Action " << actidx << " breaks closure: "), act) << '\n';
        }
      }
      else if (!(act_pf & sys.invariant).subseteq_ck(sys.shadow_pfmla | sys.shadow_self)) {
        add = false;
        if (false) {
          OPut((DBogOF << "Action " << actidx << " breaks shadow protocol: "), act) << '\n';
        }
      }
    }

    if (add) {
      candidates.push_back(actidx);
    }
  }
  if (candidates.size() == 0) {
    DBog0( "No candidates actions!" );
    return false;
  }

  return true;
}

/**
 * Check if two actions can coexist in a
 * deterministic protocol of self-disabling processes.
 */
  bool
coexist_ck(const Xn::ActSymm& a, const Xn::ActSymm& b)
{
  if (a.pc_symm != b.pc_symm)  return true;
  const Xn::PcSymm& pc = *a.pc_symm;

  bool enabling = true;
  bool deterministic = false;
  for (uint j = 0; enabling && j < pc.rvbl_symms.sz(); ++j) {
    if (a.guard(j) != b.guard(j)) {
      deterministic = true;
      if (!pc.write_ck(j)) {
        enabling = false;
      }
    }
  }

  if (!deterministic)  return false;
  if (!enabling)  return true;

  bool a_enables = true;
  bool b_enables = true;
  for (uint j = 0; j < pc.wvbl_symms.sz(); ++j) {
    if (a.assign(j) != b.aguard(j)) {
      a_enables = false;
    }
    if (b.assign(j) != a.aguard(j)) {
      b_enables = false;
    }
  }
  return !(a_enables || b_enables);
}

/** Rank the deadlocks by how many actions can resolve them.*/
  void
RankDeadlocksMCV(vector<DeadlockConstraint>& dlsets,
                 const Xn::Net& topo,
                 const vector<uint>& actions,
                 const PF& deadlockPF)
{
  dlsets.clear();
  dlsets.push_back(DeadlockConstraint(deadlockPF));

  for (uint i = 0; i < actions.size(); ++i) {
    PF guard( topo.action_pfmla(actions[i]).pre() );

    for (uint j = dlsets.size(); j > 0; --j) {
      PF resolved( dlsets[j-1].deadlockPF & guard );

      if (!resolved.tautology_ck(false)) {
        dlsets[j-1].deadlockPF -= resolved;
        if (j == dlsets.size()) {
          dlsets.push_back(DeadlockConstraint(resolved));
        }
        else {
          dlsets[j].deadlockPF |= resolved;
        }
      }
    }
  }

  for (uint i = 0; i < actions.size(); ++i) {
    PF guard( topo.action_pfmla(actions[i]).pre() );
    for (uint j = 0; j < dlsets.size(); ++j) {
      if (!(guard & dlsets[j].deadlockPF).tautology_ck(false)) {
        dlsets[j].candidates |= actions[i];
      }
    }
  }

  if (DBog_RankDeadlocksMCV) {
    for (uint i = 0; i < dlsets.size(); ++i) {
      if (!dlsets[i].deadlockPF.tautology_ck(false)) {
        DBog2( "Rank %u has %u actions.", i, (uint) dlsets[i].candidates.size() );
      }
    }
  }
}

/**
 * Revise the ranks of deadlocks which are ranked by number candidate actions
 * which can resolve them.
 * \param adds  Actions which were added to the program.
 * \param dels  Actions which were pruned from the list of candidates.
 */
  void
ReviseDeadlocksMCV(vector<DeadlockConstraint>& dlsets,
                   const Xn::Net& topo,
                   const Set<uint>& adds,
                   const Set<uint>& dels)
{
  PF addGuardPF(false);
  PF delGuardPF(false);
  for (Set<uint>::const_iterator it = adds.begin(); it != adds.end(); ++it) {
    addGuardPF |= topo.action_pfmla(*it).pre();
  }
  for (Set<uint>::const_iterator it = dels.begin(); it != dels.end(); ++it) {
    delGuardPF |= topo.action_pfmla(*it).pre();
  }

  for (uint i = 1; i < dlsets.size(); ++i) {
    Set<uint>& candidates1 = dlsets[i].candidates;
    PF& deadlockPF1 = dlsets[i].deadlockPF;

    Set<uint> addCandidates( candidates1 & adds );
    Set<uint> delCandidates( candidates1 & dels );

    Set<uint> diffCandidates1; // To remove from this rank.

    diffCandidates1 = (candidates1 & addCandidates);
    if (!diffCandidates1.empty()) {
      candidates1 -= diffCandidates1;
      diffCandidates1.clear();

      deadlockPF1 -= addGuardPF;
      Set<uint>::iterator it;
      for (it = candidates1.begin(); it != candidates1.end(); ++it) {
        uint actId = *it;
        const PF& candidateGuardPF = topo.action_pfmla(actId);
        if (!deadlockPF1.overlap_ck(candidateGuardPF)) {
          // Action no longer resolves any deadlocks in this rank.
          diffCandidates1 |= actId;
        }
      }
      candidates1 -= diffCandidates1;
    }

    diffCandidates1 = (candidates1 & delCandidates);
    if (!diffCandidates1.empty()) {
      const PF& diffDeadlockPF1 = (deadlockPF1 & delGuardPF);
      deadlockPF1 -= diffDeadlockPF1;

      vector<DeadlockConstraint>
        diffDeadlockSets( i+1, DeadlockConstraint(PF(false)) );
      diffDeadlockSets[i].deadlockPF = diffDeadlockPF1;

      Set<uint>::iterator it;

      uint minIdx = i;
      for (it = diffCandidates1.begin(); it != diffCandidates1.end(); ++it) {
        const uint actId = *it;
        const PF& candidateGuardPF = topo.action_pfmla(actId).pre();
        for (uint j = minIdx; j < diffDeadlockSets.size(); ++j) {
          const PF& diffPF =
            (candidateGuardPF & diffDeadlockSets[j].deadlockPF);
          if (!diffPF.tautology_ck(false)) {
            diffDeadlockSets[j-1].deadlockPF |= diffPF;
            diffDeadlockSets[j].deadlockPF -= diffPF;
            if (j == minIdx) {
              -- minIdx;
            }
          }
        }
      }

      candidates1 -= diffCandidates1;
      diffCandidates1.clear();
      diffDeadlockSets[i].deadlockPF = deadlockPF1;

      for (it = candidates1.begin(); it != candidates1.end(); ++it) {
        const uint actId = *it;
        const PF& candidateGuardPF = topo.action_pfmla(actId).pre();
        if (!candidateGuardPF.overlap_ck(diffDeadlockPF1)) {
          // This candidate is not affected.
          diffDeadlockSets[i].candidates |= actId;
          continue;
        }
        for (uint j = minIdx; j < diffDeadlockSets.size(); ++j) {
          if (candidateGuardPF.overlap_ck(diffDeadlockSets[j].deadlockPF)) {
            diffDeadlockSets[j].candidates |= actId;
          }
        }
      }

      for (uint j = minIdx; j < i; ++j) {
        dlsets[j].deadlockPF |= diffDeadlockSets[j].deadlockPF;
        dlsets[j].candidates |= diffDeadlockSets[j].candidates;
      }
      candidates1 &= diffDeadlockSets[i].candidates;
    }
  }
}

/**
 * Pick the next candidate action to use.
 * The most constrained variable (MCV) heuristic may be used.
 *
 * \param ret_actidx  Return value. Action to use.
 * \param dlsets  Deadlock sets ordered by number of
 *   resolving candidate actions.
 * \param backReachPF  Backwards reachability from invariant.
 * \return True iff an action was picked. It should return
 *   true unless you're doing it wrong).
 */
  bool
PickActionMCV(uint& ret_actidx,
              const Xn::Sys& sys,
              const StabilitySynLvl& tape,
              const AddConvergenceOpt& opt)
{
  typedef AddConvergenceOpt Opt;
  const Opt::PickActionHeuristic& pick_method = opt.pick_method;
  const Opt::NicePolicy& nicePolicy = opt.nicePolicy;

  const Xn::Net& topo = sys.topology;
  const vector<DeadlockConstraint>& dlsets = tape.mcvDeadlocks;
  uint dlsetIdx = 0;

  if (pick_method == Opt::RandomPick) {
    uint idx = tape.ctx->urandom.pick(tape.candidates.size());
    ret_actidx = tape.candidates[idx];
    return true;
  }

  Set<uint> candidates;
  Set<uint>::const_iterator it;

  // Do most constrained variable (MCV).
  // That is, find an action which resolves a deadlock which
  // can only be resolved by some small number of actions.
  // Try to choose an action which adds a new path to the invariant.
  for (uint i = 0; i < dlsets.size(); ++i) {
    if (!dlsets[i].candidates.empty()) {
      candidates = dlsets[i].candidates;
      if (opt.pickBackReach) {
        Set<uint> candidates_1;
        for (it = candidates.begin(); it != candidates.end(); ++it) {
          const uint actId = *it;
          const PF& resolveImg =
            topo.action_pfmla(actId).img(dlsets[i].deadlockPF);
          if (tape.backReachPF.overlap_ck(resolveImg)) {
            candidates_1 |= actId;
          }
        }
        candidates = candidates_1;
        if (candidates.empty())  continue;
      }
      dlsetIdx = i;
      break;
    }
  }


  if (tape.bt_dbog) {
    DBogOF
      <<" (lvl " << tape.bt_level
      << ") (mcv " << dlsetIdx
      << ") (mcv-sz " << candidates.size()
      << ")\n";
    DBogOF.flush();
  }

  Map< uint, Set<uint> > biasMap;
  bool biasToMax = true;

  if (nicePolicy == Opt::BegNice) {
    // Only consider actions of highest priority process.
    bool have = false;
    uint niceIdxMin = 0;
    Set<uint> candidates_1;
    for (it = candidates.begin(); it != candidates.end(); ++it) {
      const uint actId = *it;
      const uint pcId = topo.action_pcsymm_index(actId);
      const uint niceIdx = sys.niceIdxOf(pcId);
      if (!have || (niceIdx < niceIdxMin)) {
        have = true;
        candidates_1.clear();
        candidates_1 |= actId;
        niceIdxMin = niceIdx;
      }
    }
    candidates = candidates_1;
  }

  if (pick_method == Opt::GreedyPick || pick_method == Opt::GreedySlowPick) {
    biasToMax = true;

    Map< uint, uint > resolveMap;
    for (uint j = dlsetIdx; j < dlsets.size(); ++j) {
      const Set<uint>& resolveSet = (candidates & dlsets[j].candidates);
      for (it = resolveSet.begin(); it != resolveSet.end(); ++it) {
        const uint actId = *it;

        uint w = 0; // Weight.
        if (pick_method != Opt::GreedySlowPick) {
          w = j;
        }
        else {
          Set<uint>::const_iterator jt;
          const PF& actPF = topo.action_pfmla(*it);
          for (jt = dlsets[j].candidates.begin();
               jt != dlsets[j].candidates.end();
               ++jt) {
            const uint actId2 = *jt;
            if (actId == actId2) {
              continue;
            }
            const PF& preAct2 = topo.action_pfmla(actId2).pre();
            if (dlsets[j].deadlockPF.overlap_ck(actPF & preAct2)) {
              ++ w;
            }
          }
        }

        uint* n = resolveMap.lookup(actId);
        if (!n) {
          resolveMap[actId] = w;
        }
        else {
          *n += w;
        }
      }
    }

    for (it = candidates.begin(); it != candidates.end(); ++it) {
      const uint actId = *it;
      uint n = *resolveMap.lookup(actId);
#if 0
      const PF& backReachPF = tape.backReachPF;
      if (backReachPF.overlap_ck(topo.action_pfmla(actId).img())) {
        if (!(topo.action_pfmla(actId).pre() <= backReachPF)) {
          n += dlsets.size() * dlsets.size();
        }
      }
#endif
      biasMap[n] |= actId;
    }
  }
  else if (pick_method == Opt::LCVLitePick) {
    biasToMax = false;

    for (it = candidates.begin(); it != candidates.end(); ++it) {
      const uint actId = *it;
      uint n = 0;
      vector<DeadlockConstraint> tmpDeadlocks( dlsets );
      ReviseDeadlocksMCV(tmpDeadlocks, topo, Set<uint>(actId), Set<uint>());
      for (uint j = 1; j < tmpDeadlocks.size(); ++j) {
        n += tmpDeadlocks[j].candidates.size();
      }

      biasMap[n] |= actId;
    }
  }
  else if (pick_method == Opt::LCVHeavyPick) {
    biasToMax = false;

    for (it = candidates.begin(); it != candidates.end(); ++it) {
      const uint actId = *it;
      StabilitySynLvl next( tape );
      next.bt_dbog = false;
      uint n = tape.candidates.size();
      if (next.revise_actions(sys, Set<uint>(actId), Set<uint>()))
      {
        n -= next.candidates.size();
        n /= (next.actions.size() - tape.actions.size());
      }
      //uint n = next.candidates.size() + next.actions.size();
      //uint n = 0;
      //for (uint j = 1; j < next.mcvDeadlocks.size(); ++j) {
      //  n += next.mcvDeadlocks[j].candidates.size() / j;
      //}

      biasMap[n] |= actId;
    }
  }
  else if (pick_method == Opt::LCVJankPick) {
    biasToMax = true;
    Map< uint, Set<uint> > overlapSets;

    for (it = candidates.begin(); it != candidates.end(); ++it) {
      overlapSets[*it] = Set<uint>(*it);
    }

    const PF& deadlockPF = dlsets[dlsetIdx].deadlockPF;
    for (it = candidates.begin(); it != candidates.end(); ++it) {
      uint actId = *it;
      const PF& actPF = topo.action_pfmla(actId);
      const PF actPrePF = actPF.pre();

      Set<uint>& overlapSet = *overlapSets.lookup(actId);

      Set<uint>::const_iterator jt = it;
      for (++jt; jt != candidates.end(); ++jt) {
        const uint actId2 = *jt;
        const PF& actPF2 = topo.action_pfmla(actId2);
        if (deadlockPF.overlap_ck(actPrePF & actPF2.pre())) {
          overlapSet |= actId2;
          *overlapSets.lookup(actId2) |= actId;
        }
      }
    }

    bool have = false;
    Set<uint> minOverlapSet;

    Map< uint,Set<uint> >::const_iterator mit;
    for (mit = overlapSets.begin(); mit != overlapSets.end(); ++mit) {
      const Set<uint>& overlapSet = mit->second;
      if (!have || overlapSet.size() < minOverlapSet.size()) {
        have = true;
        minOverlapSet = overlapSet;
      }
    }

    DBog2("(lvl %u) (size %u)", tape.bt_level, minOverlapSet.size());

    for (it = minOverlapSet.begin(); it != minOverlapSet.end(); ++it) {
      const uint actId = *it;
      StabilitySynLvl next( tape );
      next.bt_dbog = false;
      uint n = 0;
      if (next.revise_actions(sys, Set<uint>(actId), Set<uint>()))
        n = next.candidates.size();
      //uint n = next.candidates.size() + next.actions.size();
      //uint n = 0;
      //for (uint j = 1; j < next.mcvDeadlocks.size(); ++j) {
      //  n += next.mcvDeadlocks[j].candidates.size() / j;
      //}
      biasMap[n] |= actId;
    }
  }
  else if (pick_method == Opt::ConflictPick) {
    biasToMax = false;
    FlatSet<uint> membs;
    tape.ctx->conflicts.superset_membs(membs, FlatSet<uint>(tape.picks),
                                       FlatSet<uint>(tape.candidates));
    if (membs.overlap_ck(candidates)) {
      biasMap[0] = (candidates & Set<uint>(membs));
    }
#if 0
    else if (membs.sz() > 0) {
      uint idx = tape.ctx->urandom.pick(membs.sz());
      biasMap[0] |= membs[idx];
    }
#endif
    else {
      biasMap[0] |= candidates;
    }
  }
  else if (pick_method == Opt::QuickPick) {
    biasToMax = false;
    const PF& backReachPF = tape.backReachPF;
    for (it = candidates.begin(); it != candidates.end(); ++it) {
      uint actId = *it;
      const PF& actPF = topo.action_pfmla(actId);
      if (sys.shadow_puppet_synthesis_ck()) {
        if (!actPF.overlap_ck(tape.hi_invariant)) {
          biasMap[0] |= actId;
        }
        else {
          biasMap[1] |= actId;
        }
        continue;
      }
      if (backReachPF.overlap_ck(actPF.img())) {
        biasMap[1] |= actId;
        if (!(actPF.pre() <= backReachPF)) {
          biasMap[0] |= actId;
        }
      }
      else {
        biasMap[2] |= actId;
      }
    }
  }

  if (!biasMap.empty()) {
    const std::pair< uint, Set<uint> >& entry =
      (biasToMax ? *biasMap.rbegin() : *biasMap.begin());
    candidates = entry.second;
  }
  else {
    DBog0( "Bad News: biasMap is empty!!!" );
    return false;
  }

  if (opt.random_one_shot) {
    vector<uint> candidates_vec;
    candidates.fill(candidates_vec);
    uint idx = tape.ctx->urandom.pick(candidates_vec.size());
    ret_actidx = candidates_vec[idx];
  }
  else if (nicePolicy == Opt::EndNice) {
    bool have = false;
    uint niceIdxMin = 0;
    uint extremeActId = 0;
    Set<uint>::const_iterator it;
    for (it = candidates.begin(); it != candidates.end(); ++it) {
      const uint actId = *it;
      const uint pcId = topo.action_pcsymm_index(actId);
      const uint niceIdx = sys.niceIdxOf(pcId);
      if (!have || (niceIdx < niceIdxMin)) {
        have = true;
        niceIdxMin = niceIdx;
        extremeActId = actId;
      }
    }
    ret_actidx = extremeActId;
  }
  else {
    ret_actidx = candidates.elem();
  }
  return true;
}

/**
 * Do trivial trimming of the candidate actions after using an action.
 * The pruned candidate actions would break our assumption that processes are
 * self-disabling and deterministic.
 */
  void
QuickTrim(Set<uint>& delSet,
          const vector<uint>& candidates,
          const Xn::Net& topo,
          uint actId)
{
  Xn::ActSymm act0;
  topo.action(act0, actId);
  Xn::ActSymm act1;
  for (uint i = 0; i < candidates.size(); ++i) {
    topo.action(act1, candidates[i]);
    if (!coexist_ck(act0, act1)) {
      delSet |= candidates[i];
    }
  }
}

  void
small_cycle_conflict (Cx::Table<uint>& conflict_set,
                      const Cx::PFmla& scc,
                      const vector<uint>& actions,
                      const Xn::Net& topo,
                      const Cx::PFmla& invariant)
{
  conflict_set.clear();

  Cx::PFmla edg( false );
  Cx::Table<uint> scc_actidcs;
  for (uint i = 0; i < actions.size(); ++i) {
    uint actidx = actions[i];
    const Cx::PFmla& act_pfmla = topo.action_pfmla(actidx);
    if (scc.overlap_ck(act_pfmla)) {
      if (scc.overlap_ck(act_pfmla.img())) {
        edg |= act_pfmla;
        scc_actidcs.push(actidx);
      }
    }
  }

  // Go in reverse so actions chosen at earlier levels are more likely
  // to be used in conflict set.
  for (uint i = scc_actidcs.sz(); i > 0;) {
    i -= 1;
    uint actidx = scc_actidcs[i];
    const Cx::PFmla& act_pfmla = topo.action_pfmla(actidx);
    Cx::PFmla next_scc(false);
    if (cycle_ck(&next_scc, edg - act_pfmla, scc)
        && invariant.overlap_ck(next_scc))
    {
        edg -= act_pfmla;
    }
    else
    {
      conflict_set.push(actidx);
    }
  }
  //Claim( cycle_ck(edg, scc) );
}

  uint
count_actions_in_cycle (const Cx::PFmla& scc, Cx::PFmla edg,
                        const vector<uint>& actions, const Xn::Net& topo)
{
  uint n = 1;
  Cx::Table<uint> scc_actidcs;
  for (uint i = 0; i < actions.size(); ++i) {
    const Cx::PFmla& act_pfmla = topo.action_pfmla(actions[i]);
    if (scc.overlap_ck(act_pfmla)) {
      if (scc.overlap_ck(act_pfmla.img())) {
        edg |= act_pfmla;
        scc_actidcs.push(actions[i]);
        ++ n;
      }
    }
  }
  uint nneed = 1;
  uint nmin = 1;
  Cx::PFmla min_edg = edg;
  for (uint i = 0; i < scc_actidcs.size(); ++i) {
    const Cx::PFmla& act_pfmla = topo.action_pfmla(scc_actidcs[i]);
    if (!cycle_ck(edg - act_pfmla, scc)) {
      ++ nneed;
      ++ nmin;
    }
    else {
      if (cycle_ck(min_edg - act_pfmla, min_edg)) {
        min_edg -= act_pfmla;
      }
      else {
        ++ nmin;
      }
    }
  }
  DBog1("needed:%u", nneed);
  DBog1("nmin:%u", nmin);
  return n;
}

  uint
StabilitySynLvl::add_small_conflict_set(const Xn::Sys& sys,
                                        const Cx::Table<uint>& delpicks)
{
  if (noconflicts)  return 0;
  if (false || directly_add_conflicts) {
    this->ctx->conflicts.add_conflict(delpicks);
    return 0;
  }
  Set<uint> delpick_set( delpicks );
  for (uint i = 0; i < delpicks.sz(); ++i) {
    StabilitySynLvl lvl( *this->ctx->base_lvl );
    lvl.bt_dbog = false;
    lvl.noconflicts = true;
    delpick_set -= delpicks[i];
    if (lvl.revise_actions(sys, delpick_set, Set<uint>())) {
      delpick_set |= delpicks[i];
    }
  }
  this->ctx->conflicts.add_conflict(delpick_set);
  return delpick_set.sz();
}

#if 0
/** Detect cycles added by new action when we have the transitive
 * closure of all actions so far. This is a fast check, but computing
 * the transitive closure takes a long time since it a set of transitions
 * rather than just states.
 */
static
  bool
reach_cycle_ck (const Cx::PFmla& reach, const Cx::PFmla& act_pf, const Cx::PFmla& state_pf)
{
  const Cx::PFmla& trim_reach = act_pf.img() & act_pf.pre().as_img() & reach;

  Cx::PFmla next( state_pf & trim_reach.img() );
  Cx::PFmla pf( false );
  while (!pf.equiv_ck(next))
  {
    pf = next;
    next &= trim_reach.img(act_pf.img(next));
  }
  return pf.sat_ck();
}
#endif

/** Infer and prune actions from candidate list.**/
  bool
StabilitySynLvl::check_forward(const Xn::Sys& sys)
{
  const Xn::Net& topo = sys.topology;
  const Cx::PFmla& invariant = this->hi_invariant;

  if (this->mcvDeadlocks.size() <= 1) {
    // This should have been caught if no deadlocks remain.
    Claim(this->deadlockPF.tautology_ck(false));
    this->candidates.clear();
    return true;
  }
  Set<uint> adds;
  Set<uint> dels;
  adds |= this->mcvDeadlocks[1].candidates;

  Set<uint> action_set( this->actions );
  action_set |= adds;

  for (uint i = 0; i < this->candidates.size(); ++i) {
    if  (ctx->done && *ctx->done)
      return true;

    uint actidx = this->candidates[i];
    if (dels.elem_ck(actidx))  continue;

    const PF& act_pf = topo.action_pfmla(actidx);
    if (!this->deadlockPF.overlap_ck(act_pf.pre())) {
      if (false && this->bt_dbog) {
        Xn::ActSymm act;
        DBog0("DEAD PRUNE!");
        DBogOF
          << "DEL (lvl " << this->bt_level
          << ") (sz " << this->actions.size()
          << ") (rem " << this->candidates.size()
          << ")  ";
        topo.action(act, actidx);
        OPut(DBogOF, act) << '\n';
        DBogOF.flush();
      }
      dels |= actidx;
      continue;
    }

    action_set |= actidx;
    bool conflict_found =
      this->ctx->conflicts.conflict_ck(FlatSet<uint>(action_set));
    action_set -= Set<uint>(actidx);
    if (conflict_found) {
      dels |= actidx;
      continue;
    }

  }
  if (!adds.empty() || !dels.empty()) {
#if 0
    Cx::Table<uint> delpicks( this->picks );
    Set<uint>::const_iterator it = dels.begin();
    for (;it != dels.end(); ++it)
    {
      delpicks.push(*it);
      this->add_small_conflict_set(sys, delpicks);
      delpicks.mpop(1);
    }
#endif

    return this->revise_actions(sys, adds, dels);
  }
  return true;
}

/** Add actions to protocol and delete actions from candidate list.**/
  bool
StabilitySynLvl::revise_actions(const Xn::Sys& sys,
                                Set<uint> adds,
                                Set<uint> dels)
{
  const Xn::Net& topo = sys.topology;
  Xn::ActSymm act;
  Set<uint>::const_iterator it;
  const bool use_csp = false;

  adds |= this->mcvDeadlocks[1].candidates;

  PF addActPF( false );
  for (it = adds.begin(); it != adds.end(); ++it) {
    uint actId = *it;
    if (use_csp) {
      this->csp_pfmla &=
        this->ctx->csp_pfmla_ctx.vbl(topo.action_pre_index(actId))
        == topo.action_img_index(actId);
    }

    if (!Remove1(this->candidates, actId)) {
      // Not applicable.
      return false;
    }
    this->actions.push_back(actId);
    QuickTrim(dels, this->candidates, topo, actId);
    addActPF |= topo.action_pfmla(actId);
  }

  if (!(adds & dels).empty()) {
    if ((adds & dels) <= this->mcvDeadlocks[1].candidates)
    {
      if (this->bt_dbog)
        DBog0( "Conflicting add from MCV." );
    }
    else
    {
      DBog0( "Tried to add conflicting actions... this is not good!!!" );
    }
    return false;
  }

  this->loXnRel |= addActPF;
  this->deadlockPF -= addActPF.pre();

  PF delActPF( false );
  for (it = dels.begin(); it != dels.end(); ++it) {
    uint actId = *it;
    if (use_csp) {
      this->csp_pfmla &=
        this->ctx->csp_pfmla_ctx.vbl(topo.action_pre_index(actId))
        != topo.action_img_index(actId);
    }
    Remove1(this->candidates, actId);
    delActPF |= topo.action_pfmla(actId);
  }
  this->hiXnRel -= delActPF;

  for (it = adds.begin(); it != adds.end(); ++it) {
    uint actId = *it;
    if (this->bt_dbog) {
      DBogOF
        << " (lvl " << this->bt_level
        << ") (sz " << this->actions.size()
        << ") (rem " << this->candidates.size()
        << ")  ";
      topo.action(act, actId);
      OPut(DBogOF, act) << '\n';
      DBogOF.flush();
    }
  }

  Cx::PFmla scc(false);
  cycle_ck(&scc, this->loXnRel);
  if (!scc.subseteq_ck(sys.invariant)) {
    //uint n = count_actions_in_cycle(scc, act_pf, this->actions, topo);
    //DBog1("scc actions: %u", n);
    if (this->bt_dbog) {
      DBogOF << "CYCLE\n";
    }
    if (!this->noconflicts) {
      Cx::Table<uint> conflict_set;
      small_cycle_conflict (conflict_set, scc, this->actions, topo, sys.invariant);
      this->ctx->conflicts.add_conflict(conflict_set);
    }
    return false;
  }

  if (sys.shadow_puppet_synthesis_ck()) {
    this->hi_invariant =
      LegitInvariant(sys, this->loXnRel, this->hiXnRel, &scc);
    if (!this->hi_invariant.sat_ck()) {
      if (this->bt_dbog) {
        DBogOF << "LEGIT\n";
      }
      return false;
    }
  }
  else {
    this->hi_invariant = sys.invariant;
  }

  if (!WeakConvergenceCk(sys, this->hiXnRel, this->hi_invariant)) {
    if (this->bt_dbog) {
      DBogOF << "REACH\n";
    }
    return false;
  }

  this->backReachPF =
    BackwardReachability(this->loXnRel, this->hi_invariant);


  bool revise = true;
  if (sys.shadow_puppet_synthesis_ck()) {
    RankDeadlocksMCV(this->mcvDeadlocks,
                     sys.topology,
                     this->candidates,
                     this->deadlockPF);
    revise = false;
  }

  if (revise) {
    ReviseDeadlocksMCV(this->mcvDeadlocks, topo, adds, dels);
  }

  return this->check_forward(sys);
}

  bool
StabilitySynLvl::pick_action(const Xn::Sys& sys, uint act_idx)
{
  this->picks.push(act_idx);
  if (!this->revise_actions(sys, Set<uint>(act_idx), Set<uint>())) {
    this->add_small_conflict_set(sys, this->picks);
    return false;
  }
  return true;
}

