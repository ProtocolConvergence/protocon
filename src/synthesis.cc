
#include "synthesis.hh"

#include "cx/fileb.hh"
#include "cx/tuple.hh"
#include "prot-ofile.hh"

#include <algorithm>

#include "namespace.hh"

/**
 * Check if two actions can coexist in a
 * deterministic protocol of self-disabling processes.
 */
  bool
coexist_ck(const Xn::ActSymm& a, const Xn::ActSymm& b,
           const Xn::Net& topo,
           bool force_disabling, bool pure_actions)
{
  if (a.pc_symm != b.pc_symm)  return true;
  const Xn::PcSymm& pc = *a.pc_symm;

  bool pure_shadow_img_eql = true;
  bool puppet_adj_eql = true;
  for (uint i = 0; i < pc.rvbl_symms.sz(); ++i) {
    if (!pc.write_flags[i] && pc.rvbl_symms[i]->puppet_ck()) {
      if (a.guard(i) != b.guard(i))
        puppet_adj_eql = false;
    }
  }

  bool puppet_img_eql = true;
  bool random_write = false;
  for (uint i = 0; i < pc.wvbl_symms.sz(); ++i) {
    if (pc.spec->random_write_flags[pc.wmap[i]])
      random_write = true;
    if (pc.wvbl_symms[i]->puppet_ck()) {
      if (a.assign(i) != b.assign(i))
        puppet_img_eql = false;
    }
    else {
      if (pc.wvbl_symms[i]->domsz != a.assign(i) &&
          pc.wvbl_symms[i]->domsz != b.assign(i) &&
          a.assign(i) != b.assign(i)) {
        pure_shadow_img_eql = false;
      }
    }
  }

  if (puppet_adj_eql && puppet_img_eql && !pure_shadow_img_eql)
    return false;

  if (pure_actions && puppet_adj_eql && !puppet_img_eql)
    return false;

  bool enabling = true;
  bool deterministic = false;
  for (uint j = 0; enabling && j < pc.rvbl_symms.sz(); ++j) {
    if (pc.rvbl_symms[j]->pure_shadow_ck())
      continue;
    if (a.guard(j) != b.guard(j)) {
      deterministic = true;
      if (!pc.write_ck(j) && !pc.spec->random_read_flags[j]) {
        enabling = false;
      }
    }
  }

  if (!deterministic)  return false;
  if (!enabling)  return true;
  if (random_write)  return true;

  bool shadow_exists = false;
  bool a_self_loop = true;
  bool b_self_loop = true;
  bool a_enables = true;
  bool b_enables = true;
  for (uint j = 0; j < pc.wvbl_symms.sz(); ++j) {
    if (pc.wvbl_symms[j]->pure_shadow_ck()) {
      shadow_exists = true;
      continue;
    }
    if (a.assign(j) != a.aguard(j)) {
      a_self_loop = false;
    }
    if (b.assign(j) != b.aguard(j)) {
      b_self_loop = false;
    }
    if (a.assign(j) != b.aguard(j)) {
      a_enables = false;
    }
    if (b.assign(j) != a.aguard(j)) {
      b_enables = false;
    }
  }

  if (!shadow_exists && (a_self_loop || b_self_loop)) {
    return false;
  }
  if (a_enables && !b_self_loop) {
    if (force_disabling)  return false;
    Xn::ActSymm ab = a;
    const uint off = pc.rvbl_symms.sz();
    for (uint j = off; j < ab.vals.sz(); ++j) {
      ab.vals[j] = b.vals[j];
    }
    return !topo.safe_ck(ab);
  }
  if (b_enables && !a_self_loop) {
    if (force_disabling)  return false;
    Xn::ActSymm ba = b;
    const uint off = pc.rvbl_symms.sz();
    for (uint j = off; j < ba.vals.sz(); ++j) {
      ba.vals[j] = a.vals[j];
    }
    return !topo.safe_ck(ba);
  }
  return true;
}

  void
RankDeadlocksMRV(vector<DeadlockConstraint>& dlsets,
                 const Xn::Net& topo,
                 const vector<uint>& candidates,
                 const P::Fmla& deadlockPF)
{
  dlsets.clear();
  if (!deadlockPF.sat_ck())  return;
  dlsets.push_back(DeadlockConstraint(deadlockPF));
  for (uint cidx = 0; cidx < candidates.size(); ++cidx) {
    uint actidx = candidates[cidx];
    const P::Fmla& act_pre = topo.action_pfmla(actidx).pre();
    uint i = dlsets.size();
    while (i > 0) {
      i -= 1;
      P::Fmla resolved = dlsets[i].deadlockPF & act_pre;
      if (resolved.sat_ck()) {
        if (i == dlsets.size()-1) {
          dlsets.push_back(DeadlockConstraint(P::Fmla(false)));
        }
        dlsets[i].deadlockPF -= resolved;
        dlsets[i+1].deadlockPF |= resolved;
      }
    }
  }
  for (uint cidx = 0; cidx < candidates.size(); ++cidx) {
    uint actidx = candidates[cidx];
    const P::Fmla& act_pre = topo.action_pfmla(actidx).pre();
    for (uint i = 0; i < dlsets.size(); ++i) {
      if (act_pre.overlap_ck(dlsets[i].deadlockPF)) {
        dlsets[i].candidates << actidx;
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
ReviseDeadlocksMRV(vector<DeadlockConstraint>& dlsets,
                   const Xn::Net& topo,
                   const Set<uint>& adds,
                   const Set<uint>& dels)
{
  P::Fmla addGuardPF(false);
  P::Fmla delGuardPF(false);
  for (Set<uint>::const_iterator it = adds.begin(); it != adds.end(); ++it) {
    addGuardPF |= topo.action_pfmla(*it).pre();
  }
  for (Set<uint>::const_iterator it = dels.begin(); it != dels.end(); ++it) {
    delGuardPF |= topo.action_pfmla(*it).pre();
  }

  for (uint i = 1; i < dlsets.size(); ++i) {
    Set<uint>& candidates1 = dlsets[i].candidates;
    P::Fmla& deadlockPF1 = dlsets[i].deadlockPF;

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
        const P::Fmla& candidateGuardPF = topo.action_pfmla(actId);
        if (!deadlockPF1.overlap_ck(candidateGuardPF)) {
          // Action no longer resolves any deadlocks in this rank.
          diffCandidates1 << actId;
        }
      }
      candidates1 -= diffCandidates1;
    }

    diffCandidates1 = (candidates1 & delCandidates);
    if (!diffCandidates1.empty()) {
      const P::Fmla& diffDeadlockPF1 = (deadlockPF1 & delGuardPF);
      deadlockPF1 -= diffDeadlockPF1;

      vector<DeadlockConstraint>
        diffDeadlockSets( i+1, DeadlockConstraint(P::Fmla(false)) );
      diffDeadlockSets[i].deadlockPF = diffDeadlockPF1;

      Set<uint>::iterator it;

      uint minidx = i;
      for (it = diffCandidates1.begin(); it != diffCandidates1.end(); ++it) {
        const uint actId = *it;
        const P::Fmla& candidateGuardPF = topo.action_pfmla(actId).pre();
        Claim( minidx > 0 && "BUG! Don't use -fast-deadlock-mrv flag." );
        for (uint j = minidx; j < diffDeadlockSets.size(); ++j) {
          const P::Fmla& diffPF =
            (candidateGuardPF & diffDeadlockSets[j].deadlockPF);
          if (diffPF.sat_ck()) {
            diffDeadlockSets[j-1].deadlockPF |= diffPF;
            diffDeadlockSets[j].deadlockPF -= diffPF;
            if (j == minidx) {
              -- minidx;
            }
          }
        }
      }

      candidates1 -= diffCandidates1;
      diffCandidates1.clear();
      diffDeadlockSets[i].deadlockPF = deadlockPF1;

      for (it = candidates1.begin(); it != candidates1.end(); ++it) {
        const uint actId = *it;
        const P::Fmla& candidateGuardPF = topo.action_pfmla(actId).pre();
        if (!candidateGuardPF.overlap_ck(diffDeadlockPF1)) {
          // This candidate is not affected.
          diffDeadlockSets[i].candidates << actId;
          continue;
        }
        for (uint j = minidx; j < diffDeadlockSets.size(); ++j) {
          if (candidateGuardPF.overlap_ck(diffDeadlockSets[j].deadlockPF)) {
            diffDeadlockSets[j].candidates << actId;
          }
        }
      }

      for (uint j = minidx; j < i; ++j) {
        dlsets[j].deadlockPF |= diffDeadlockSets[j].deadlockPF;
        dlsets[j].candidates |= diffDeadlockSets[j].candidates;
      }
      candidates1 &= diffDeadlockSets[i].candidates;
    }
  }
}

static void
pick_action_candidates(Set<uint>& ret_candidates,
                       const PartialSynthesis& inst,
                       const AddConvergenceOpt& opt,
                       uint dlset_idx);

/**
 * Pick the next candidate action to use.
 * The minimum remaining values (MRV) heuristic may be used.
 *
 * \param ret_actidx  Return value. Action to use.
 * \return True iff an action was picked. It should return
 *   true unless you're doing it wrong).
 */
  bool
PickActionMRV(uint& ret_actidx,
              const PartialSynthesis& partial,
              const AddConvergenceOpt& opt)
{
  typedef AddConvergenceOpt Opt;
  const Opt::PickActionHeuristic& pick_method = opt.pick_method;

  if (pick_method == Opt::FullyRandomPick) {
    for (uint inst_idx = 0; inst_idx < partial.sz(); ++inst_idx) {
      if (partial[inst_idx].candidates.size() > 0) {
        uint idx = partial[inst_idx].ctx->urandom.pick(partial[inst_idx].candidates.size());
        ret_actidx = partial[inst_idx].candidates[idx];
        return true;
      }
    }
    return false;
  }

  // Do minimal remaining values heuristic (MRV).
  // That is, find an action which resolves a deadlock which
  // can only be resolved by some small number of actions.
  uint mrv_dlset_idx = 0;
  for (uint inst_idx = 0; inst_idx < partial.sz(); ++inst_idx) {
    if (partial[inst_idx].no_partial)  continue;
    const PartialSynthesis& inst = partial[inst_idx];
    for (uint i = 0; i < inst.mcv_deadlocks.size(); ++i) {
      if (mrv_dlset_idx > 0 && i >= mrv_dlset_idx)
        break;
      const Set<uint>& inst_candidates = inst.mcv_deadlocks[i].candidates;
      if (!inst_candidates.empty())
        mrv_dlset_idx = i;
    }
  }
  Set<uint> candidates;
  uint mcv_inst_idx = 0;
  for (uint inst_idx = 0; inst_idx < partial.sz(); ++inst_idx) {
    if (partial[inst_idx].no_partial)
      continue;
    const PartialSynthesis& inst = partial[inst_idx];
    if (mrv_dlset_idx >= inst.mcv_deadlocks.size())
      continue;
    Claim2( mrv_dlset_idx ,<, inst.mcv_deadlocks.size() );
    const Set<uint>& inst_candidates = inst.mcv_deadlocks[mrv_dlset_idx].candidates;
    if (inst_candidates.empty())
      continue;

    Set<uint> tmp_candidates;
    pick_action_candidates(tmp_candidates, inst, opt, mrv_dlset_idx);
    if (tmp_candidates.sz() == 0)
      return false;

    if (candidates.sz() == 0 || tmp_candidates.sz() < candidates.sz()) {
      mcv_inst_idx = inst_idx;
      candidates = tmp_candidates;
    }
  }

  if (candidates.sz() == 0) {
    for (uint inst_idx = 0; inst_idx < partial.sz(); ++inst_idx) {
      if (partial[inst_idx].candidates.size() > 0) {
        candidates |= Set<uint>(partial[inst_idx].candidates);
        mcv_inst_idx = inst_idx;
        break;
      }
    }
  }
  Claim2( candidates.sz() ,>, 0 );

  vector<uint> candidates_vec;
  candidates.fill(candidates_vec);

  const Xn::Net& topo = partial.ctx->systems[0]->topology;
  // When using randomization, always use the action with
  // the lowest randomized values in its guard.
  // (Actions with lower values have lower ids/indices.)
  if (topo.probabilistic_ck())
  {
    Set<uint> tmp_set;
    for (uint i=0; i < candidates_vec.size(); ++i) {
      const uint actidx = candidates_vec[i];
      Xn::ActSymm act;
      topo.action(act, actidx);
      const Xn::PcSymm& pc_symm = *act.pc_symm;

      for (uint j = 0; j < pc_symm.rvbl_symms.sz(); ++j) {
        if (pc_symm.spec->random_read_flags[j] || pc_symm.spec->random_write_flags[j]) {
          act.vals[j] = 0;
        }
      }
      uint tmp_actidx = topo.action_index(act);
      if (!tmp_set.elem_ck(tmp_actidx)) {
        tmp_set << tmp_actidx;
      }
      else {
        candidates.erase(actidx);
      }
    }
    candidates.fill(candidates_vec);
  }

  const PartialSynthesis& inst = partial[mcv_inst_idx];
  *inst.log
    << " (lvl " << inst.bt_level
    << ") (psys " << inst.sys_idx
    << ") (mrv " << mrv_dlset_idx
    << ") (mrv-sz "
    << (mrv_dlset_idx == 0 ? 0 :
        inst.mcv_deadlocks[mrv_dlset_idx].candidates.sz())
    << ") (rem-sz " << candidates.sz()
    << ")" << inst.log->endl();

  if (opt.randomize_pick && opt.randomize_depth <= inst.bt_level) {
    uint idx = inst.ctx->urandom.pick(candidates_vec.size());
    ret_actidx = candidates_vec[idx];
  }
  else {
    ret_actidx = candidates.elem();
  }
  return true;
}

  void
pick_action_candidates(Set<uint>& ret_candidates,
                       const PartialSynthesis& inst,
                       const AddConvergenceOpt& opt,
                       uint dlset_idx)
{

  typedef AddConvergenceOpt Opt;
  const Opt::PickActionHeuristic& pick_method = opt.pick_method;
  const Opt::NicePolicy& nicePolicy = opt.nicePolicy;
  const Xn::Sys& sys = *inst.ctx->systems[inst.sys_idx];
  const Xn::Net& topo = sys.topology;

  Set<uint> candidates( inst.mcv_deadlocks[dlset_idx].candidates );
  const vector<DeadlockConstraint>& dlsets = inst.mcv_deadlocks;

  Set<uint>::const_iterator it;

  // Try to choose an action which adds a new path to the invariant.
  if (opt.pick_back_reach) {
    const P::Fmla reach_pf = inst.lo_xn.pre_reach(inst.hi_invariant);
    Set<uint> candidates_1;
    for (it = candidates.begin(); it != candidates.end(); ++it) {
      const uint actidx = *it;
      const P::Fmla& resolve_img =
        topo.action_pfmla(actidx).img(dlsets[dlset_idx].deadlockPF);
      if (reach_pf.overlap_ck(resolve_img)) {
        candidates_1 << actidx;
      }
    }
    candidates = candidates_1;
    if (candidates.empty()) {
      candidates = dlsets[dlset_idx].candidates;
    }
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
        candidates_1 << actId;
        niceIdxMin = niceIdx;
      }
      else if (niceIdx == niceIdxMin) {
        candidates_1 << actId;
      }
    }
    candidates = candidates_1;
  }

  if (pick_method == Opt::MRVLitePick) {
    biasMap[0] = candidates;
  }
  else if (pick_method == Opt::LexPick) {
    // Use the lexicographically "first" MRV set.
    biasToMax = false;

    P::Fmla deadlock_pf = dlsets[dlset_idx].deadlockPF;

    for (it = candidates.begin(); it != candidates.end(); ++it) {
      const uint act_id = *it;
      const P::Fmla& act_pre = topo.action_pfmla(act_id).pre();
      if (deadlock_pf.overlap_ck(act_pre)) {
        deadlock_pf &= act_pre;
        biasMap[0] << act_id;
      }
      else {
        biasMap[1] << act_id;
      }
    }
  }
  else if (pick_method == Opt::GreedyPick || pick_method == Opt::GreedySlowPick) {
    biasToMax = true;

    Map< uint, uint > resolveMap;
    for (uint j = dlset_idx; j < dlsets.size(); ++j) {
      const Set<uint>& resolveSet = (candidates & dlsets[j].candidates);
      for (it = resolveSet.begin(); it != resolveSet.end(); ++it) {
        const uint actId = *it;

        uint w = 0; // Weight.
        if (pick_method != Opt::GreedySlowPick) {
          w = j;
        }
        else {
          Set<uint>::const_iterator jt;
          const X::Fmla& actPF = topo.action_pfmla(*it);
          for (jt = dlsets[j].candidates.begin();
               jt != dlsets[j].candidates.end();
               ++jt) {
            const uint actId2 = *jt;
            if (actId == actId2) {
              continue;
            }
            const P::Fmla& preAct2 = topo.action_pfmla(actId2).pre();
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
      biasMap[n] << actId;
    }
  }
  else if (pick_method == Opt::LCVLitePick) {
    biasToMax = false;

    for (it = candidates.begin(); it != candidates.end(); ++it) {
      const uint actId = *it;
      uint n = 0;
      vector<DeadlockConstraint> tmpDeadlocks( dlsets );
      ReviseDeadlocksMRV(tmpDeadlocks, topo, Set<uint>(actId), Set<uint>());
      for (uint j = 1; j < tmpDeadlocks.size(); ++j) {
        n += tmpDeadlocks[j].candidates.size();
      }

      biasMap[n] << actId;
    }
  }
  else if (pick_method == Opt::LCVHeavyPick) {
    biasToMax = false;

    for (it = candidates.begin(); it != candidates.end(); ++it) {
      const uint actId = *it;
      PartialSynthesis next( inst );
      next.log = &OFile::null();
      uint n = inst.candidates.size();
      if (next.revise_actions(Set<uint>(actId), Set<uint>()))
      {
        n -= next.candidates.size();
        n /= (next.actions.size() - inst.actions.size());
      }
      //uint n = next.candidates.size() + next.actions.size();
      //uint n = 0;
      //for (uint j = 1; j < next.mcv_deadlocks.size(); ++j) {
      //  n += next.mcv_deadlocks[j].candidates.size() / j;
      //}

      biasMap[n] << actId;
    }
  }
  else if (pick_method == Opt::LCVJankPick) {
    biasToMax = true;
    Map< uint, Set<uint> > overlapSets;

    for (it = candidates.begin(); it != candidates.end(); ++it) {
      overlapSets[*it] = Set<uint>(*it);
    }

    const P::Fmla& deadlockPF = dlsets[dlset_idx].deadlockPF;
    for (it = candidates.begin(); it != candidates.end(); ++it) {
      uint actId = *it;
      const X::Fmla& actPF = topo.action_pfmla(actId);
      const P::Fmla actPrePF = actPF.pre();

      Set<uint>& overlapSet = *overlapSets.lookup(actId);

      Set<uint>::const_iterator jt = it;
      for (++jt; jt != candidates.end(); ++jt) {
        const uint actId2 = *jt;
        const X::Fmla& actPF2 = topo.action_pfmla(actId2);
        if (deadlockPF.overlap_ck(actPrePF & actPF2.pre())) {
          overlapSet << actId2;
          *overlapSets.lookup(actId2) << actId;
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

    DBog2("(lvl %u) (size %u)", inst.bt_level, minOverlapSet.size());

    for (it = minOverlapSet.begin(); it != minOverlapSet.end(); ++it) {
      const uint actId = *it;
      PartialSynthesis next( inst );
      next.log = &OFile::null();
      uint n = 0;
      if (next.revise_actions(Set<uint>(actId), Set<uint>()))
        n = next.candidates.size();
      //uint n = next.candidates.size() + next.actions.size();
      //uint n = 0;
      //for (uint j = 1; j < next.mcv_deadlocks.size(); ++j) {
      //  n += next.mcv_deadlocks[j].candidates.size() / j;
      //}
      biasMap[n] << actId;
    }
  }
  else if (pick_method == Opt::ConflictPick) {
    biasToMax = false;
    FlatSet<uint> membs;
    inst.ctx->conflicts.superset_membs(membs, FlatSet<uint>(inst.picks),
                                       FlatSet<uint>(inst.candidates));
    if (membs.overlap_ck(candidates)) {
      biasMap[0] = (candidates & Set<uint>(membs));
    }
#if 0
    else if (membs.sz() > 0) {
      uint idx = inst.ctx->urandom.pick(membs.sz());
      biasMap[0] << membs[idx];
    }
#endif
    else {
      biasMap[0] |= candidates;
    }
  }
  else if (pick_method == Opt::QuickPick) {
    const P::Fmla reach_pf = inst.lo_xn.pre_reach(inst.hi_invariant);
    biasToMax = false;
    for (it = candidates.begin(); it != candidates.end(); ++it) {
      uint actId = *it;
      const X::Fmla& act_pf = topo.action_pfmla(actId);
      if (sys.shadow_puppet_synthesis_ck()) {
        if (!act_pf.overlap_ck(inst.hi_invariant)) {
          biasMap[0] << actId;
        }
        else {
          biasMap[1] << actId;
        }
        continue;
      }
      if (reach_pf.overlap_ck(act_pf.img())) {
        biasMap[1] << actId;
        if (!(act_pf.pre() <= reach_pf)) {
          biasMap[0] << actId;
        }
      }
      else {
        biasMap[2] << actId;
      }
    }
  }

  if (!biasMap.empty()) {
    const std::pair< uint, Set<uint> >& entry =
      (biasToMax ? *biasMap.rbegin() : *biasMap.begin());
    candidates = entry.second;
  }
  else {
    ret_candidates.clear();
    DBog0( "Bad News: biasMap is empty!!!" );
    return;
  }

  if (nicePolicy == Opt::EndNice) {
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
        candidates_1 << actId;
        niceIdxMin = niceIdx;
      }
      else if (niceIdx == niceIdxMin) {
        candidates_1 << actId;
      }
    }
    candidates = candidates_1;
  }
  ret_candidates = candidates;
}

/**
 * Do trivial trimming of the candidate actions after using an action.
 * The pruned candidate actions would break our assumption that processes are
 * self-disabling and deterministic.
 */
static
  void
QuickTrim(Set<uint>& delSet,
          const vector<uint>& candidates,
          uint actidx,
          const Xn::Net& topo,
          bool force_disabling,
          bool pure_actions)
{
  const Table<uint>& represented = topo.represented_actions[actidx];

  Xn::ActSymm act0;
  Xn::ActSymm act1;
  for (uint i = 0; i < candidates.size(); ++i) {
    if (candidates[i] == actidx)  continue;

    topo.action(act1, candidates[i]);
    //Claim( !represented.elem_ck(candidates[i]) );

    for (uint j = 0; j < represented.sz(); ++j) {
      topo.action(act0, represented[j]);
      if (!coexist_ck(act0, act1, topo, force_disabling, pure_actions)) {
        delSet << candidates[i];
        break;
      }
    }
  }
}

static
  void
small_cycle_conflict (Table<uint>& conflict_set,
                      const P::Fmla& scc,
                      const vector<uint>& actions,
                      const Xn::Net& topo,
                      const P::Fmla& invariant,
                      const SynthesisCtx& synctx)
{
  conflict_set.clear();

  X::Fmla edg( false );
  Table<uint> scc_actidcs;
  Table<X::Fmla> xn_pfmlas(1, X::Fmla(false));
  for (uint i = 0; i < actions.size(); ++i) {
    uint actidx = actions[i];
    const X::Fmla& act_pfmla = topo.action_pfmla(actidx);
    if (scc.overlap_ck(act_pfmla)) {
      if (scc.overlap_ck(act_pfmla.img())) {
        scc_actidcs.push(actidx);
        edg |= act_pfmla;
        xn_pfmlas.push(edg);
      }
    }
  }

  edg = false;

  // Go in reverse so actions chosen at earlier levels are more likely
  // to be used in conflict set.
  for (uint i = scc_actidcs.sz(); i > 0;) {
    i -= 1;
    P::Fmla next_scc(false);
    if (synctx.done_ck()) {
      while (i > 0) {
        conflict_set.push(scc_actidcs[i]);
        --i;
      }
      break;
    }

    if ((edg | xn_pfmlas[i]).cycle_ck(&next_scc, scc)
        && invariant.overlap_ck(next_scc))
    {
    }
    else
    {
      uint actidx = scc_actidcs[i];
      const X::Fmla& act_pfmla = topo.action_pfmla(actidx);
      conflict_set.push(actidx);
      edg |= act_pfmla;
    }
  }
  //Claim( edg.cycle_ck(scc) );
}

  uint
count_actions_in_cycle (const P::Fmla& scc, X::Fmla edg,
                        const vector<uint>& actions, const Xn::Net& topo)
{
  uint n = 1;
  Table<uint> scc_actidcs;
  for (uint i = 0; i < actions.size(); ++i) {
    const X::Fmla& act_pfmla = topo.action_pfmla(actions[i]);
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
  X::Fmla min_edg = edg;
  for (uint i = 0; i < scc_actidcs.size(); ++i) {
    const X::Fmla& act_pfmla = topo.action_pfmla(scc_actidcs[i]);
    if (!(edg - act_pfmla).cycle_ck(scc)) {
      ++ nneed;
      ++ nmin;
    }
    else {
      if ((min_edg - act_pfmla).cycle_ck(min_edg)) {
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

  const StabilizationOpt&
PartialSynthesis::stabilization_opt() const
{
  return ctx->stabilization_opts[sys_idx];
}

  uint
PartialSynthesis::add_small_conflict_set(const Table<uint>& delpicks)
{
  if (this->ctx->done_ck())
    return delpicks.sz();

  bool doit = false;
  for (uint i = 0; i < this->sz(); ++i) {
    if (!(*this)[i].no_conflict) {
      doit = true;
    }
  }
  if (!doit)  return 0;
  ConflictFamily& conflicts = this->ctx->conflicts;
  if (this->ctx->opt.max_conflict_sz > 0 &&
      delpicks.sz() > this->ctx->opt.max_conflict_sz) {
    return delpicks.sz();
  }
  if (conflicts.conflict_ck(Cx::FlatSet<uint>(delpicks))) {
    if (!conflicts.exact_conflict_ck(Cx::FlatSet<uint>(delpicks))) {
      *this->log << "Conflict subsumed by existing one." << this->log->endl();
      return delpicks.sz();
    }
  }
  conflicts.add_conflict(delpicks);
  if (directly_add_conflicts) {
    return delpicks.sz();
  }
  Set<uint> delpick_set( delpicks );
  for (uint i = 0; i < delpicks.sz(); ++i) {
    PartialSynthesis partial( this->ctx->base_partial );
    for (uint j = 0; j < partial.sz(); ++j) {
      partial[j].log = &OFile::null();
      partial[j].directly_add_conflicts = true;
      if (partial[j].no_conflict) {
        partial[j].no_partial = true;
      }
    }
    delpick_set -= delpicks[i];
    if (partial.revise_actions(delpick_set, Set<uint>(delpicks[i]))) {
      delpick_set << delpicks[i];
    }
    else {
      if (this->ctx->done_ck()) {
        delpick_set << delpicks[i];
        break;
      }
      conflicts.add_conflict(delpick_set);
    }
  }
  *this->log << "Conflict size:" << delpick_set.sz() << this->log->endl();
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
reach_cycle_ck (const P::Fmla& reach, const X::Fmla& act_pf, const P::Fmla& state_pf)
{
  const P::Fmla& trim_reach = act_pf.img() & act_pf.pre().as_img() & reach;

  P::Fmla next( state_pf & trim_reach.img() );
  P::Fmla pf( false );
  while (!pf.equiv_ck(next))
  {
    pf = next;
    next &= trim_reach.img(act_pf.img(next));
  }
  return pf.sat_ck();
}
#endif

  void
PartialSynthesis::useless_picks(Map<uint,uint>& changes, Set<uint>& allowed) const
{
  const Xn::Sys& sys = *this->ctx->systems[this->sys_idx];
  const Xn::Net& topo = sys.topology;
  Set<uint> dels;
  for (Set<uint>::const_iterator it = allowed.begin(); it != allowed.end(); ++it) {
    uint actidx = *it;
    if (!allowed.elem_ck(actidx))  continue;
    Xn::ActSymm act;
    topo.action(act, actidx);
    const Xn::PcSymm& pc_symm = *act.pc_symm;
    const X::Fmla& act_xn = topo.action_pfmla(actidx);
    if (pc_symm.shadow_pfmla.sat_ck() && !act_xn.pre().overlap_ck(this->hi_invariant)) {
      bool changed = false;
      for (uint vidx = 0; vidx < pc_symm.wvbl_symms.sz(); ++vidx) {
        const Xn::VblSymm& vbl_symm = *pc_symm.wvbl_symms[vidx];
        if (!vbl_symm.pure_shadow_ck())
          continue;
        if (act.assign(vidx) != vbl_symm.domsz) {
          changed = true;
          act.vals[pc_symm.rvbl_symms.sz() + vidx] = vbl_symm.domsz;
        }
      }
      if (changed) {
        changes[actidx] = topo.action_index(act);
      }
      else {
        dels << actidx;
      }
    }
  }
  allowed -= dels;
}

/** Infer and prune actions from candidate list.**/
  bool
PartialSynthesis::check_forward(Set<uint>& adds, Set<uint>& dels, Set<uint>& rejs)
{
  Claim(!this->no_partial);
  const Xn::Sys& sys = *this->ctx->systems[this->sys_idx];
  const Xn::Net& topo = sys.topology;

  if (this->mcv_deadlocks.size() <= 1) {
    Claim(!this->deadlockPF.sat_ck());
    this->candidates.clear();
    if (this->ctx->conflicts.conflict_ck(FlatSet<uint>(this->actions))) {
      *this->log << "CONFLICT" << this->log->endl();
      return false;
    }
    return true;
  }
  adds |= this->mcv_deadlocks[1].candidates;

  const P::Fmla& lo_xn_pre = this->lo_xn.pre();
  for (uint i = 0; i < this->candidates.size(); ++i) {
    uint actidx = this->candidates[i];
    if (dels.elem_ck(actidx))  continue;

    bool keep = true;

    Xn::ActSymm act;
    topo.action(act, actidx);
    const Xn::PcSymm& pc_symm = *act.pc_symm;

    const X::Fmla& act_xn = topo.action_pfmla(actidx);

    if (keep && act_xn.subseteq_ck(lo_xn_pre)) {
      keep = false;
    }
    if (keep && pc_symm.shadow_pfmla.sat_ck() &&
        !sys.spec->active_shadow_ck() &&
        !act_xn.pre().overlap_ck(this->hi_invariant)) {
      // If the protocol is not silent, actions used only for convergence
      // do not need to change shadow variables.
      for (uint vidx = 0; vidx < pc_symm.wvbl_symms.sz(); ++vidx) {
        const Xn::VblSymm& vbl_symm = *pc_symm.wvbl_symms[vidx];
        if (!vbl_symm.pure_shadow_ck())
          continue;
        if (act.assign(vidx) != vbl_symm.domsz) {
          keep = false;
          break;
        }
      }
    }

    if (!keep) {
      dels << actidx;
    }
    if (!keep && false) {
      *this->log
        << "DEL (lvl " << this->bt_level
        << ") (sz " << this->actions.size()
        << ") (rem " << this->candidates.size()
        << ")  ";
      OPut(*this->log, act) << this->log->endl();
    }
  }

  FlatSet<uint> action_set( Set<uint>(this->actions) | adds );
  FlatSet<uint> candidate_set( this->candidates );

  Set<uint> membs;
  if (!this->ctx->conflicts.conflict_membs(&membs, action_set, candidate_set)) {
    *this->log << "CONFLICT" << this->log->endl();
    return false;
  }
  dels |= membs;
  rejs |= membs;

  return true;
}

/** Add actions to protocol and delete actions from candidate list.**/
  bool
PartialSynthesis::revise_actions_alone(Set<uint>& adds, Set<uint>& dels,
                                       Set<uint>& rejs, uint* ret_nlayers)
{
  bool candidates_contain_all_adds = true;
  const Xn::Sys& sys = *this->ctx->systems[this->sys_idx];
  const Xn::Net& topo = sys.topology;
  Set<uint>::const_iterator it;
  const bool use_csp = false;

  if (this->ctx->done_ck())
    return false;

  // For debug only. Optimized out.
  for (uint i = 0; false && i < this->candidates.size(); ++i) {
    Xn::ActSymm act;
    *this->log << "candidate " << (i+1) << "/" << this->candidates.size() << ": ";
    topo.action(act, candidates[i]);
    OPut(*this->log, act);
    *this->log << this->log->endl();
  }

  if (this->ctx->opt.prep_conflicts) {
    FlatSet<uint> action_set( Set<uint>(this->actions) | adds );
    FlatSet<uint> candidate_set( this->candidates );

    Set<uint> membs;
    if (!this->ctx->conflicts.conflict_membs(&membs, action_set, candidate_set)) {
      *this->log << "CONFLICT" << this->log->endl();
      return false;
    }
    dels |= membs;
  }

  if (this->no_partial) {
    X::Fmlae add_act_xfmlae( &topo.xfmlae_ctx );

    for (it = adds.begin(); it != adds.end(); ++it) {
      uint actidx = *it;
      Remove1(this->candidates, actidx);
      Remove1(this->actions, actidx);
      this->actions.push_back(actidx);
      add_act_xfmlae |= topo.action_xfmlae(actidx);
    }
    for (it = dels.begin(); it != dels.end(); ++it) {
      uint actidx = *it;
      Remove1(this->candidates, actidx);
    }
    adds.clear();
    dels.clear();
    if (ret_nlayers) {
      *ret_nlayers = 1;
    }

    this->lo_xfmlae |= add_act_xfmlae;
    this->deadlockPF =
      ((~sys.invariant | sys.shadow_pfmla.pre()) & sys.closed_assume)
      - this->lo_xfmlae.pre();

    return (this->candidates.size() > 0 || !this->deadlockPF.sat_ck());
  }

  X::Fmlae add_act_xfmlae( &topo.xfmlae_ctx );
  for (it = adds.begin(); it != adds.end(); ++it) {
    uint actId = *it;
    if (use_csp) {
      this->csp_pfmla &=
        this->ctx->csp_pfmla_ctx.vbl(topo.action_pre_index(actId))
        == topo.action_img_index(actId);
    }

    if (!Remove1(this->candidates, actId)) {
      candidates_contain_all_adds = false;
      // This action wasn't a candidate,
      // but that may just mean it introduces nondeterminism
      // or doesn't resolve any existing deadlocks.
    }
    Remove1(this->actions, actId); // No duplicates
    this->actions.push_back(actId);
    add_act_xfmlae |= topo.action_xfmlae(actId);

    if (!this->ctx->opt.prep_conflicts) {
      Set<uint> tmp_dels;
      QuickTrim(tmp_dels, this->candidates, actId,
                topo,
                this->ctx->opt.force_disabling,
                this->ctx->opt.pure_actions);
      if (tmp_dels.overlap_ck(adds)) {
        tmp_dels -= adds;
      }
      if (false && tmp_dels.size() > 0) {
        *this->log << "QuickTrim() rejects an action!!!" << this->log->endl();
        Set<uint>::const_iterator del_it;
        for (del_it = tmp_dels.begin(); del_it != tmp_dels.end(); ++del_it) {
          Xn::ActSymm act;
          topo.action(act, actId);
          *this->log
            << " (sys " << this->sys_idx
            << ") (lvl " << this->bt_level
            << ") (sz " << this->actions.size()
            << ") (rem " << this->candidates.size()
            << ")  ";
          OPut(*this->log, act) << this->log->endl();
          FlatSet<uint> tmp_adds_dels( adds & tmp_dels );
          for (uint i = 0; i < tmp_adds_dels.sz(); ++i) {
            *this->log << "Reject:" << this->log->endl();
            topo.action(act, tmp_adds_dels[i]);
            OPut(*this->log, act) << this->log->endl();
          }
        }
      }
      dels |= tmp_dels;
    }
  }

  if (adds.overlap_ck(dels)) {
    if ((adds & dels) <= this->mcv_deadlocks[1].candidates)
    {
      *this->log << "Conflicting add from MRV." << this->log->endl();
    }
    else
    {
      *this->log << "Tried to add conflicting actions... this is not good!!!" << this->log->endl();
    }
    if (true) {
      FlatSet<uint> adds_dels( adds & dels );
      for (uint i = 0; i < adds_dels.sz(); ++i) {
        Xn::ActSymm act;
        topo.action(act, adds_dels[i]);
        *this->log << "Reject:" << this->log->endl();
        OPut(*this->log, act) << this->log->endl();
      }
    }
    return false;
  }

  if (this->stabilization_opt().synchronous) {
    this->lo_xn = topo.sync_xn(Table<uint>(this->actions));
    if (!this->lo_xn.img(sys.closed_assume).subseteq_ck(sys.closed_assume)) {
      *this->log << "SYNC_BREAKS_ASSUME" << this->log->endl();
      return false;
    }
  }
  else {
    this->lo_xn |= add_act_xfmlae.xfmla();
  }
  this->lo_xfmlae |= add_act_xfmlae;
  if (!candidates_contain_all_adds) {
    this->hi_xn |= add_act_xfmlae.xfmla();
    this->hi_xfmlae |= add_act_xfmlae;
  }
  Xn::ActSymm act;
  if (this->sys_idx == 0)
  for (it = adds.begin(); it != adds.end(); ++it) {
    uint actId = *it;
    *this->log
      << " (lvl " << this->bt_level
      << ") (sz " << this->actions.size()
      << ") (rem " << this->candidates.size()
      << ")  ";
    topo.action(act, actId);
    OPut(*this->log, act) << this->log->endl();
  }

  X::Fmla del_act_xn( false );
  Table<P::Fmla> del_xns;
  for (it = dels.begin(); it != dels.end(); ++it) {
    uint actidx = *it;
    if (use_csp) {
      this->csp_pfmla &=
        this->ctx->csp_pfmla_ctx.vbl(topo.action_pre_index(actidx))
        != topo.action_img_index(actidx);
    }
    Remove1(this->candidates, actidx);
    del_act_xn |= topo.action_pfmla(actidx);
    del_xns.push(topo.action_pfmla(actidx));
    if (false) {
      Xn::ActSymm act;
      DBogOF << "DEL ";
      topo.action(act, actidx);
      OPut(DBogOF, act) << DBogOF.endl();
    }
  }
  del_act_xn -= this->lo_xn;
  for (uint i = 0; i < this->candidates.size(); ++i) {
    del_act_xn -= topo.action_pfmla(this->candidates[i]);
  }

  this->hi_xn -= del_act_xn;


  uint max_nlayers = this->stabilization_opt().max_nlayers;
  if (ret_nlayers && *ret_nlayers > 0
      && (max_nlayers == 0 || *ret_nlayers < max_nlayers))
  {
    max_nlayers = *ret_nlayers;
  }
  uint nlayers = max_nlayers;
  P::Fmla scc(false);
  if (topo.probabilistic_ck()) {
    nlayers = 1;
    P::Fmla tmp_invariant = lo_xn.closure_within(sys.invariant);
    lo_xfmlae.probabilistic_livelock_ck(&scc, sys.closed_assume, (~tmp_invariant).cross(tmp_invariant), &lo_xn);
  }
  else if (this->stabilization_opt().uniring) {
    lo_xfmlae.uniring_cycle_ck(&scc, &nlayers, &this->hi_invariant, &sys.closed_assume);
  }
  else {
    lo_xn.cycle_ck(&scc, &nlayers, &this->hi_invariant, &sys.closed_assume);
  }
  if (max_nlayers > 0 && nlayers > max_nlayers) {
    *this->log << "NLAYERS (maximum number of convergence layers exceeded: "
      << nlayers << "+ > " << max_nlayers << ")" << this->log->endl();
    *this->log << "NLAYERS sys_idx:" << this->sys_idx << " nlayers:" << nlayers << this->log->endl();
    return false;
  }
  if (ret_nlayers) {
    *ret_nlayers = nlayers;
  }
  if (!scc.subseteq_ck(sys.invariant)) {
    //topo.oput_vbl_names(*this->log);
    //oput_one_cycle(*this->log, this->lo_xn, scc, scc - sys.invariant, topo);
    //uint n = count_actions_in_cycle(scc, act_pf, this->actions, topo);
    //DBog1("scc actions: %u", n);
    *this->log << "CYCLE" << this->log->endl();
    if (true || !this->no_conflict) {
      Table<uint> conflict_set;
      if (!topo.probabilistic_ck() && !this->stabilization_opt().synchronous) {
#if 0
        small_cycle_conflict (conflict_set, scc, this->actions, topo, sys.invariant,
                              *this->ctx);
#else
        conflict_set = this->actions;
        find_livelock_actions (conflict_set, this->lo_xn, scc, sys.invariant, topo);
#endif
        this->ctx->conflicts.add_conflict(conflict_set);
        *this->log << "cycle conflict size:" << conflict_set.sz() << this->log->endl();
      }
    }
    if (!!this->ctx->opt.livelock_ofilepath && &sys == this->ctx->systems.top()) {
      bool big_livelock = true;
      for (uint i = 0; i < this->ctx->systems.sz()-1; ++i) {
        if (!stabilization_ck(OFile::null(), *this->ctx->systems[i],
                              this->ctx->stabilization_opts[i], actions))
        {
          *this->log << "still issues in system " << i << this->log->endl();
          big_livelock = false;
          break;
        }
      }
      if (big_livelock) {
        Cx::OFileB ofb;
        ofb.open(this->ctx->opt.livelock_ofilepath + "." + this->ctx->opt.sys_pcidx + "." + this->ctx->opt.n_livelock_ofiles++);
        oput_protocon_file(ofb, sys, this->actions, false, "livelock");
      }
    }
    return false;
  }

  const P::Fmla old_hi_invariant( this->hi_invariant );
  if (!shadow_ck(&this->hi_invariant, sys, this->lo_xn, this->hi_xn, this->lo_xfmlae, scc))
  {
    *this->log << "SHADOW" << this->log->endl();
    return false;
  }
  if (true || candidates_contain_all_adds) {
    Claim(this->hi_invariant.subseteq_ck(old_hi_invariant));
  }

  const P::Fmla old_deadlock_pfmla( this->deadlockPF );

  // This grows sometimes when {hi_invariant} shrinks.
  this->deadlockPF =
    (((~this->hi_invariant) | sys.shadow_pfmla.pre()) & sys.closed_assume)
    - this->lo_xn.pre();

  if (!this->deadlockPF.subseteq_ck(this->hi_xn.pre())) {
    *this->log << "DEADLOCK" << this->log->endl();
    if (false) {
      topo.oput_vbl_names(*this->log);
      topo.oput_one_pf(*this->log, this->deadlockPF - this->hi_xn.pre());
      this->log->flush();
    }
    return false;
  }

  nlayers = max_nlayers;

  if (this->stabilization_opt().uniring) {
    if (!hi_xfmlae.uniring_weak_convergence_ck(&nlayers, this->hi_invariant, sys.closed_assume)) {
      *this->log << "REACH" << this->log->endl();
      return false;
    }
  }
  else if (!weak_convergence_ck(&nlayers, this->hi_xn, this->hi_invariant, sys.closed_assume)) {
    *this->log << "REACH" << this->log->endl();
#if 0
    P::Fmla pf( ~this->hi_xn.pre_reach(this->hi_invariant) );
    pf = pf.pick_pre();
    pf = this->hi_xn.img_reach(pf);
    topo.oput_all_pf(*this->log, pf);
    topo.oput_all_xn(*this->log, this->hi_xn);
#endif
    return false;
  }
  if (ret_nlayers) {
    if (*ret_nlayers < nlayers)
      *ret_nlayers = nlayers;
  }

  bool revise = true;
  if (!this->ctx->opt.fast_deadlock_mrv
      ||
      (sys.shadow_puppet_synthesis_ck() &&
       !this->deadlockPF.subseteq_ck(old_deadlock_pfmla))
      ||
      !candidates_contain_all_adds
     )
  {
    RankDeadlocksMRV(this->mcv_deadlocks,
                     sys.topology,
                     this->candidates,
                     this->deadlockPF);
    revise = false;
  }

  if (revise) {
    ReviseDeadlocksMRV(this->mcv_deadlocks, topo, adds, dels);
  }

  adds.clear();
  dels.clear();
  return this->check_forward(adds, dels, rejs);
}

  bool
PartialSynthesis::revise_actions(const Set<uint>& adds, const Set<uint>& dels,
                                 uint* ret_nlayers_sum)
{
  Table< Set<uint> > all_adds( this->sz(), adds );
  Table< Set<uint> > all_dels( this->sz(), dels );
  const uint max_nlayers_sum = this->ctx->optimal_nlayers_sum;

  // If both sets are empty, we should force a check anyway.
  bool force_revise = (adds.empty() && dels.empty());

  bool keep_going = true;
  while (keep_going) {
    keep_going = false;

    Set<uint> common_dels;

    // Generally, systems with higher indices should be more computationally intensive.
    // Therefore if {keep_going} becomes true, we should revise the systems with lower
    // indices before revising the systems with higher indices.
    for (uint i = 0; !(keep_going && common_dels.empty()) && i < this->sz(); ++i) {
      if (!force_revise && all_adds[i].empty() && all_dels[i].empty())
        continue;

      if (max_nlayers_sum > 0) {
        uint nlayers_sum = 0;
        for (uint j = 0; j < this->sz(); ++j) {
          nlayers_sum += (*this)[j].lo_nlayers;
        }
        if (nlayers_sum >= max_nlayers_sum) {
          *this->log << "SUBOPTIMAL (exceeding best known number of convergence layers: "
            << nlayers_sum << " >= " << max_nlayers_sum << ")" << this->log->endl();
          return false;
        }
        nlayers_sum -= (*this)[i].lo_nlayers;
        Claim2( nlayers_sum+1 ,<, max_nlayers_sum );
        (*this)[i].lo_nlayers = max_nlayers_sum - 1 - nlayers_sum;
      }
      else {
        (*this)[i].lo_nlayers = 0;
      }

      PartialSynthesis& partial_soln = (*this)[i];
      Set<uint> rejs;
      if (!partial_soln.revise_actions_alone(all_adds[i], all_dels[i], rejs,
                                             &(*this)[i].lo_nlayers))
        return false;
      Claim( rejs.subseteq_ck(all_dels[i]) );

      if (i==0)  common_dels  = all_dels[i];
      else       common_dels &= all_dels[i];
      all_dels[i].clear();

      if (!all_adds[i].empty() || !rejs.empty()) {
        keep_going = true;
        for (uint j = 0; j < this->sz(); ++j) {
          all_adds[j] |= all_adds[i];
          all_dels[j] |= rejs;
        }
        // Stop forcing if we'll check everything anyway.
        force_revise = false;
      }
    }

    if (!common_dels.empty()) {
      for (uint j = 0; j < this->sz(); ++j) {
        all_dels[j] |= common_dels;
      }
    }
  }

  const Xn::Sys& sys = *this->ctx->systems[this->sys_idx];
  const Xn::Net& topo = sys.topology;
  Map<uint,uint> changes;
  Set<uint> allowed_changes(this->picks);
  if (true &&
      !sys.spec->active_shadow_ck() &&
      sys.shadow_puppet_synthesis_ck()) {
    for (uint i = 0; i < this->sz(); ++i) {
      (*this)[i].useless_picks(changes, allowed_changes);
    }
  }

  if (changes.sz() > 0) {
    this->ctx->conflicts.add_conflict(this->picks);
    // Just use the first pick.
    for (uint i = 0; i < this->picks.size(); ++i) {
      Map<uint,uint>::const_iterator it = changes.find(this->picks[i]);
      if (it == changes.end())
        continue;
      uint actidx = it->first;
      uint newactidx = it->second;
      changes.clear();
      changes[actidx] = newactidx;
    }

    const Set<uint> old_actset( this->actions );
    const Table<uint> old_picks = this->picks;

    vector<uint> newpicks(this->picks.size());
    for (uint i = 0; i < this->picks.size(); ++i) {
      uint actidx = this->picks[i];
      Map<uint,uint>::const_iterator it = changes.find(actidx);
      if (it != changes.end()) {
        actidx = it->second;
      }
      newpicks[i] = actidx;
    }

    OFile* tmp_log = this->log;
    const vector<uint> old_actions = this->actions;
    for (uint i = 0; i < this->sz(); ++i) {
      PartialSynthesis& partial = (*this)[i];
      const PartialSynthesis& base_partial = this->ctx->base_partial[i];

      partial.picks = newpicks;

      partial.actions = base_partial.actions;
      partial.candidates = base_partial.candidates;
      partial.deadlockPF = base_partial.deadlockPF;
      partial.lo_xn = base_partial.lo_xn;
      partial.hi_xn = base_partial.hi_xn;
      partial.lo_xfmlae = base_partial.lo_xfmlae;
      partial.hi_xfmlae = base_partial.hi_xfmlae;
      partial.hi_invariant = base_partial.hi_invariant;
      partial.log = &OFile::null();
    }

    const Set<uint> newadds(newpicks);
    const Set<uint> newdels;
    bool consistent =
      revise_actions(newadds, newdels, ret_nlayers_sum);

    for (uint i = 0; i < this->sz(); ++i)
      (*this)[i].log = tmp_log;

    if (consistent) {
      for (uint i = 0; i < this->picks.sz(); ++i) {
        if (this->picks[i] != old_picks[i]) {
          Xn::ActSymm act;
          topo.action(act, this->picks[i]);
          OPut(*this->log << "SWAPIN ", act) << this->log->endl();
        }
      }
    }
    else {
      *this->log << "USELESS" << this->log->endl();
    }
    return consistent;
  }

  for (uint i = 0; i < this->sz()-1; ++i) {
    Claim2( (*this)[i].actions.size() ,==, (*this)[i+1].actions.size() );
  }
  if (ret_nlayers_sum) {
    uint nlayers_sum = 0;
    for (uint i = 0; i < this->sz(); ++i) {
      nlayers_sum += (*this)[i].lo_nlayers;
    }
    *ret_nlayers_sum = nlayers_sum;
  }
  return true;
}

  bool
PartialSynthesis::pick_action(uint act_idx)
{
  for (uint i = 0; i < this->sz(); ++i) {
    (*this)[i].picks.push(act_idx);
  }
  if (!this->revise_actions(Set<uint>(act_idx), Set<uint>())) {
    this->add_small_conflict_set(this->picks);
    return false;
  }

  return true;
}

  bool
PartialSynthesis::pick_actions(const vector<uint>& act_idcs)
{
  for (uint i = 0; i < this->sz(); ++i) {
    for (uint j = 0; j < act_idcs.size(); ++j) {
      (*this)[i].picks.push(act_idcs[j]);
    }
  }
  if (!this->revise_actions(Set<uint>(act_idcs), Set<uint>())) {
    this->add_small_conflict_set(this->picks);
    return false;
  }

  return true;
}

  bool
PartialSynthesis::pick_actions_separately(const vector<uint>& act_idcs,
                                          bool add_missing)
{
  DBog1("There are %u actions to pick", (uint) act_idcs.size());
  for (uint i = 0; i < act_idcs.size(); ++i) {
    DBog1("picking: %u", i);
    bool found = false;
    if (this->candidate_ck(act_idcs[i]))
      found = true;
    if (!found) {
      found = this->delegate_ck(act_idcs[i]);
      if (!add_missing) {
        if (found)
          DBog0("Already added.");
        else
          DBog0("Not a candidate!");
        continue;
      }
      if (found)  continue;
    }
    if (!found) {
      DBog0("Adding missng...");
    }
    if (!pick_action(act_idcs[i])) {
      return false;
    }
  }
  return true;
}

/**
 * Initialize synthesis structures.
 */
  bool
SynthesisCtx::init(const AddConvergenceOpt& opt)
{
  SynthesisCtx& synctx = *this;
  synctx.opt = opt;
  synctx.log = opt.log;
  urandom.use_system_urandom(opt.system_urandom);

#if 0
  const Xn::Net& topo = sys.topology;
  for (uint pcidx = 0; pcidx < topo.pc_symms.sz(); ++pcidx)
  {
    const Xn::PcSymm& pc_symm = topo.pc_symms[pcidx];
    for (uint i = 0; i < pc_symm.pre_domsz; ++i)
    {
      String name = pc_symm.spec->name + "@pre_enum[" + i + "]";
      uint vbl_idx =
        synctx.csp_pfmla_ctx.add_vbl(name, pc_symm.img_domsz);
      Claim2( vbl_idx ,==, pc_symm.pre_dom_offset + i );
    }

    Xn::ActSymm act;
    // Enforce self-disabling actions.
    if (false)
    for (uint actidx = 0; actidx < pc_symm.n_possible_acts; ++actidx) {
      pc_symm.action(act, actidx);
      synctx.csp_base_pfmla &=
        (synctx.csp_pfmla_ctx.vbl(act.pre_idx) != act.img_idx)
        |
        (synctx.csp_pfmla_ctx.vbl(act.pre_idx_of_img) == act.img_idx);
    }
  }
#endif
  return true;
}

  bool
SynthesisCtx::add(const Xn::Sys& sys, const StabilizationOpt& stabilization_opt)
{
  const Xn::Net& topo = sys.topology;
  SynthesisCtx& synctx = *this;
  if (synctx.systems.sz() > 0) {
    synctx.base_partial.instances.push( PartialSynthesis(&synctx, synctx.systems.sz()) );
  }
  synctx.systems.push(&sys);
  synctx.stabilization_opts.push(stabilization_opt);

  PartialSynthesis& partial = synctx.base_partial[synctx.base_partial.sz()-1];
  partial.log = synctx.opt.log;

  partial.csp_pfmla = synctx.csp_base_pfmla;

  Table<uint> dels;
  Table<uint> rejs;
  bool good =
    candidate_actions(partial.candidates, dels, rejs, sys);
  for (uint i = 0; i < rejs.sz(); ++i) {
    synctx.conflicts.add_impossible(rejs[i]);
  }

  for (uint pcidx = 0; pcidx < topo.pc_symms.sz(); ++pcidx) {
    const Table< FlatSet<Xn::ActSymm> >& conflicts =
      topo.pc_symms[pcidx].conflicts;
    for (uint i = 0; i < conflicts.sz(); ++i) {

      const FlatSet<Xn::ActSymm>& conflict = conflicts[i];

      Table<uint> conflict_ints(conflict.sz());
      for (uint j = 0; j < conflict.sz(); ++j) {
        Claim( conflict[j].vals.sz() > 0 );
        conflict_ints[j] = topo.action_index(conflict[j]);
      }
      synctx.conflicts.add_conflict(conflict_ints);
    }
  }

  if (!good) {
    return false;
  }
  if (synctx.opt.prep_conflicts) {
    for (uint i = 0; i < partial.candidates.size(); ++i) {
      const uint actidx = partial.candidates[i];
      Set<uint> tmp_dels;
      QuickTrim(tmp_dels, partial.candidates, actidx,
                synctx.systems[0]->topology,
                synctx.opt.force_disabling,
                synctx.opt.pure_actions);
      Table<uint> dels;
      tmp_dels.fill(dels);
      for (uint j = 0; j < dels.sz(); ++j) {
        uint conflict[2];
        conflict[0] = actidx;
        conflict[1] = dels[j];
        synctx.conflicts.add_conflict(FlatSet<uint>(conflict, 2));
      }
    }
  }

  partial.lo_xfmlae = X::Fmlae(&topo.xfmlae_ctx);
  partial.hi_xfmlae = X::Fmlae(&topo.xfmlae_ctx);

  partial.deadlockPF = ~sys.invariant & sys.closed_assume;
  partial.hi_invariant = sys.invariant & sys.closed_assume;
  if (sys.shadow_puppet_synthesis_ck()) {
    partial.deadlockPF |= sys.shadow_pfmla.pre();
  }

  if (topo.lightweight)
    return good;

  for (uint i = 0; i < partial.candidates.size(); ++i) {
    partial.hi_xfmlae |= topo.action_xfmlae(partial.candidates[i]);
  }
  partial.hi_xn = partial.hi_xfmlae.xfmla();

  RankDeadlocksMRV(partial.mcv_deadlocks,
                   sys.topology,
                   partial.candidates,
                   partial.deadlockPF);

  return good;
}

END_NAMESPACE

