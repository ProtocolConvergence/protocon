
extern "C" {
#include "cx/syscx.h"
}
#include "pfmla.hh"
#include "inst.hh"
#include "promela.hh"
#include "set.hh"
#include "test.hh"
#include "xnsys.hh"
#include <fstream>

static std::ostream& DBogOF = std::cerr;

//static const bool DBog_PruneCycles = false;
static const bool DBog_RankDeadlocksMCV = false;
static const bool DBog_PickActionMCV = false;

class DeadlockConstraint {
public:
  PF deadlockPF;
  Set<uint> candidates;
public:
  explicit DeadlockConstraint(const PF& _deadlockPF) :
    deadlockPF(_deadlockPF)
  {}
};

class AddConvergenceOpt {
public:
  enum PickActionHeuristic {
    GreedyPick,
    GreedySlowPick,
    LCVLitePick,
    LCVHeavyPick,
    LCVJankPick,
    QuickPick,
    NPickMethods
  };
  enum NicePolicy {
    NilNice,
    BegNice,
    EndNice,
    NNicePolicies
  };

  PickActionHeuristic pickMethod;
  NicePolicy nicePolicy;
  bool pickBackReach;

  AddConvergenceOpt() :
    pickMethod( GreedyPick )
    , nicePolicy( EndNice )
    , pickBackReach( true )
  {}
};

class FMem_AddConvergence {
public:
  bool bt_dbog;
  uint bt_level;

  vector<uint> actions; ///< Chosen actions.
  Set<uint> inferredActions; ///< Inferred actions.
  vector<uint> candidates; ///< Candidate actions.
  PF deadlockPF; ///< Current deadlocks.
  PF loXnRel; ///< Under-approximation of the transition function.
  PF hiXnRel; ///< Over-approximation of the transition function.
  PF backReachPF; ///< Backwards reachable from invariant.
  PF hi_invariant;

public:
  FMem_AddConvergence() :
    bt_dbog( false )
    , bt_level( 0 )
    , hi_invariant( false )
  {}

  /// Deadlocks ranked by how many candidate actions can resolve them.
  vector<DeadlockConstraint> mcvDeadlocks;

  void reviseActions(const XnSys& sys, Set<uint> adds, Set<uint> dels,
                     bool forcePrune=false);
};

/** Rank the deadlocks by how many actions can resolve them.*/
  void
RankDeadlocksMCV(vector<DeadlockConstraint>& dlsets,
                 const XnNet& topo,
                 const vector<uint>& actions,
                 const PF& deadlockPF)
{
  dlsets.clear();
  dlsets.push_back(DeadlockConstraint(deadlockPF));

  for (uint i = 0; i < actions.size(); ++i) {
    PF guard( topo.preimage(topo.actionPF(actions[i])) );

    for (uint j = dlsets.size(); j > 0; --j) {
      PF resolved( dlsets[j-1].deadlockPF & guard );

      if (!resolved.tautologyCk(false)) {
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
    PF guard( topo.preimage(topo.actionPF(actions[i])) );
    for (uint j = 0; j < dlsets.size(); ++j) {
      if (!(guard & dlsets[j].deadlockPF).tautologyCk(false)) {
        dlsets[j].candidates |= actions[i];
      }
    }
  }

  if (DBog_RankDeadlocksMCV) {
    for (uint i = 0; i < dlsets.size(); ++i) {
      if (!dlsets[i].deadlockPF.tautologyCk(false)) {
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
                   const XnNet& topo,
                   const Set<uint>& adds,
                   const Set<uint>& dels)
{
  PF addGuardPF(false);
  PF delGuardPF(false);
  for (Set<uint>::const_iterator it = adds.begin(); it != adds.end(); ++it) {
    addGuardPF |= topo.preimage(topo.actionPF(*it));
  }
  for (Set<uint>::const_iterator it = dels.begin(); it != dels.end(); ++it) {
    delGuardPF |= topo.preimage(topo.actionPF(*it));
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
        const PF& candidateGuardPF = topo.actionPF(actId);
        if (!deadlockPF1.overlapCk(candidateGuardPF)) {
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
        const PF& candidateGuardPF = topo.preimage(topo.actionPF(actId));
        for (uint j = minIdx; j < diffDeadlockSets.size(); ++j) {
          const PF& diffPF =
            (candidateGuardPF & diffDeadlockSets[j].deadlockPF);
          if (!diffPF.tautologyCk(false)) {
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
        const PF& candidateGuardPF = topo.preimage(topo.actionPF(actId));
        if (!candidateGuardPF.overlapCk(diffDeadlockPF1)) {
          // This candidate is not affected.
          diffDeadlockSets[i].candidates |= actId;
          continue;
        }
        for (uint j = minIdx; j < diffDeadlockSets.size(); ++j) {
          if (candidateGuardPF.overlapCk(diffDeadlockSets[j].deadlockPF)) {
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
 * \param ret_actId  Return value. Action to use.
 * \param dlsets  Deadlock sets ordered by number of
 *   resolving candidate actions.
 * \param backReachPF  Backwards reachability from invariant.
 * \return True iff an action was picked. It should return
 *   true unless you're doing it wrong).
 */
  bool
PickActionMCV(uint& ret_actId,
              const XnSys& sys,
              const FMem_AddConvergence& tape,
              const AddConvergenceOpt& opt)
{
  typedef AddConvergenceOpt Opt;
  const Opt::PickActionHeuristic& pickMethod = opt.pickMethod;
  const Opt::NicePolicy& nicePolicy = opt.nicePolicy;

  const XnNet& topo = sys.topology;
  const vector<DeadlockConstraint>& dlsets = tape.mcvDeadlocks;
  uint dlsetIdx = 0;

  Set<uint> candidates;
  Set<uint>::const_iterator it;

  // Do most constrained variable (MCV).
  // That is, find an action which resolves a deadlock for which
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
            topo.image(topo.actionPF(actId), dlsets[i].deadlockPF);
          if (tape.backReachPF.overlapCk(resolveImg)) {
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


  DBogOF
    <<" (lvl " << tape.bt_level
    << ") (mcv " << dlsetIdx
    << ") (mcv-sz " << candidates.size()
    << ")\n";

  map< uint, Set<uint> > biasMap;
  bool biasToMax = true;

  if (nicePolicy == Opt::BegNice) {
    // Only consider actions of highest priority process.
    bool have = false;
    uint niceIdxMin = 0;
    Set<uint> candidates_1;
    for (it = candidates.begin(); it != candidates.end(); ++it) {
      const uint actId = *it;
      const uint pcId = topo.actionPcIdx(actId);
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

  if (pickMethod == Opt::GreedyPick || pickMethod == Opt::GreedySlowPick) {
    biasToMax = true;

    map< uint, uint > resolveMap;
    for (uint j = dlsetIdx; j < dlsets.size(); ++j) {
      const Set<uint>& resolveSet = (candidates & dlsets[j].candidates);
      for (it = resolveSet.begin(); it != resolveSet.end(); ++it) {
        const uint actId = *it;

        uint w = 0; // Weight.
        if (pickMethod != Opt::GreedySlowPick) {
          w = j;
        }
        else {
          Set<uint>::const_iterator jt;
          const PF& actPF = topo.actionPF(*it);
          for (jt = dlsets[j].candidates.begin();
               jt != dlsets[j].candidates.end();
               ++jt) {
            const uint actId2 = *jt;
            if (actId == actId2) {
              continue;
            }
            const PF& preAct2 = topo.preimage(topo.actionPF(actId2));
            if (dlsets[j].deadlockPF.overlapCk(actPF & preAct2)) {
              ++ w;
            }
          }
        }

        uint* n = MapLookup(resolveMap, actId);
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
      uint n = *MapLookup(resolveMap, actId);
#if 0
      const PF& backReachPF = tape.backReachPF;
      if (backReachPF.overlapCk(topo.image(topo.actionPF(actId)))) {
        if (!(topo.preimage(topo.actionPF(actId)) <= backReachPF)) {
          n += dlsets.size() * dlsets.size();
        }
      }
#endif
      biasMap[n] |= actId;
    }
  }
  else if (pickMethod == Opt::LCVLitePick) {
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
  else if (pickMethod == Opt::LCVHeavyPick) {
    biasToMax = false;

    for (it = candidates.begin(); it != candidates.end(); ++it) {
      const uint actId = *it;
      FMem_AddConvergence next( tape );
      next.bt_dbog = false;
      next.reviseActions(sys, Set<uint>(actId), Set<uint>());
      uint n = (tape.candidates.size() - next.candidates.size());
      n /= (next.actions.size() - tape.actions.size());
      //uint n = next.candidates.size() + next.actions.size();
      //uint n = 0;
      //for (uint j = 1; j < next.mcvDeadlocks.size(); ++j) {
      //  n += next.mcvDeadlocks[j].candidates.size() / j;
      //}

      biasMap[n] |= actId;
    }
  }
  else if (pickMethod == Opt::LCVJankPick) {
    biasToMax = true;
    map< uint, Set<uint> > overlapSets;

    for (it = candidates.begin(); it != candidates.end(); ++it) {
      overlapSets[*it] = Set<uint>(*it);
    }

    const PF& deadlockPF = dlsets[dlsetIdx].deadlockPF;
    for (it = candidates.begin(); it != candidates.end(); ++it) {
      uint actId = *it;
      const PF& actPF = topo.actionPF(actId);
      const PF actPrePF = topo.preimage(actPF);

      Set<uint>& overlapSet = *MapLookup(overlapSets, actId);

      Set<uint>::const_iterator jt = it;
      for (++jt; jt != candidates.end(); ++jt) {
        const uint actId2 = *jt;
        const PF& actPF2 = topo.actionPF(actId2);
        if (deadlockPF.overlapCk(actPrePF & topo.preimage(actPF2))) {
          overlapSet |= actId2;
          *MapLookup(overlapSets, actId2) |= actId;
        }
      }
    }

    bool have = false;
    Set<uint> minOverlapSet;

    map< uint,Set<uint> >::const_iterator mit;
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
      FMem_AddConvergence next( tape );
      next.bt_dbog = false;
      next.reviseActions(sys, Set<uint>(actId), Set<uint>());

      uint n = next.candidates.size();
      //uint n = next.candidates.size() + next.actions.size();
      //uint n = 0;
      //for (uint j = 1; j < next.mcvDeadlocks.size(); ++j) {
      //  n += next.mcvDeadlocks[j].candidates.size() / j;
      //}
      biasMap[n] |= actId;
    }
  }
  else if (pickMethod == Opt::QuickPick) {
    biasToMax = false;
    const PF& backReachPF = tape.backReachPF;
    for (it = candidates.begin(); it != candidates.end(); ++it) {
      uint actId = *it;
      const PF& actPF = topo.actionPF(actId);
      if (sys.auxVblCk()) {
        if (!actPF.overlapCk(tape.hi_invariant)) {
          biasMap[0] |= actId;
        }
        else {
          biasMap[1] |= actId;
        }
        continue;
      }
      if (backReachPF.overlapCk(topo.image(actPF))) {
        biasMap[1] |= actId;
        if (!(topo.preimage(actPF) <= backReachPF)) {
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

  if (nicePolicy == Opt::EndNice) {
    bool have = false;
    uint niceIdxMin = 0;
    uint extremeActId = 0;
    Set<uint>::const_iterator it;
    for (it = candidates.begin(); it != candidates.end(); ++it) {
      const uint actId = *it;
      const uint pcId = topo.actionPcIdx(actId);
      const uint niceIdx = sys.niceIdxOf(pcId);
      if (!have || (niceIdx < niceIdxMin)) {
        have = true;
        niceIdxMin = niceIdx;
        extremeActId = actId;
      }
    }
    ret_actId = extremeActId;
  }
  else {
    ret_actId = candidates.elem();
  }
  return true;
}

/**
 * Do trivial trimming of the candidate actions after using an action.
 * The pruned candidate actions would break our assumption that processes are
 * self-disabling.
 */
  void
QuickTrim(Set<uint>& delSet,
          const vector<uint>& candidates,
          const XnNet& topo,
          uint actId)
{
  XnAct act0 = topo.action(actId);
  const XnPc& pc = topo.pcs[act0.pcIdx];
  for (uint i = 0; i < candidates.size(); ++i) {
    XnAct act1 = topo.action(candidates[i]);
    bool add = true;
    if (act0.pcIdx == act1.pcIdx) {
      bool enabling = true;
      for (uint j = 0; enabling && j < pc.rvbls.size(); ++j) {
        if (act0.r0[j] != act1.r0[j]) {
          enabling = false;
        }
      }
      bool enabling01 = enabling;
      bool enabling10 = enabling;
      for (uint j = 0; enabling && j < pc.wvbls.size(); ++j) {
        if (act0.w1[j] != act1.w0[j]) {
          enabling01 = false;
        }
        if (act1.w1[j] != act0.w0[j]) {
          enabling10 = false;
        }
        enabling = (enabling01 || enabling10);
      }
      add = !enabling;
    }
    if (!add) {
      delSet |= candidates[i];
    }
  }
}

/** Add actions to protocol and delete actions from candidate list.**/
  void
FMem_AddConvergence::reviseActions(const XnSys& sys,
                                   Set<uint> adds,
                                   Set<uint> dels,
                                   bool forcePrune)
{
  const XnNet& topo = sys.topology;
  Set<uint>::const_iterator it;

  adds |= this->mcvDeadlocks[1].candidates;

  PF addActPF( false );
  for (it = adds.begin(); it != adds.end(); ++it) {
    uint actId = *it;
    Remove1(this->candidates, actId);
    this->actions.push_back(actId);
    QuickTrim(dels, this->candidates, topo, actId);
    addActPF |= topo.actionPF(actId);
  }

  this->deadlockPF -= topo.preimage(addActPF);
  this->loXnRel |= addActPF;

  PF invariant;
  if (sys.auxVblCk()) {
    invariant = LegitInvariant(sys, this->loXnRel, this->hiXnRel);
    this->hi_invariant = invariant;
    if (invariant.tautologyCk(false)) {
      this->candidates.clear();
      return;
    }
  }
  else {
    invariant = sys.invariant;
  }
  this->backReachPF =
    BackwardReachability(this->loXnRel, invariant, topo);

  Set<uint> reqAdds;
  if (!adds.empty() || forcePrune) {
    for (uint i = 0; i < this->candidates.size(); ++i) {
      uint actId = this->candidates[i];
      if (dels.elemCk(actId))  continue;

      const PF& actPF = topo.actionPF(actId);
      if (!this->deadlockPF.overlapCk(topo.preimage(actPF))) {
        dels |= actId;
        continue;
      }

      if (sys.auxVblCk() && actPF.overlapCk(invariant)) {
        const PF& pf = ~LegitInvariant(sys, this->loXnRel | actPF, this->hiXnRel);
        if (CycleCk(topo, this->loXnRel | actPF, pf)) {
          dels |= actId;
          continue;
        }
      }
      else {
        if (CycleCk(topo, this->loXnRel | actPF, ~invariant)) {
          dels |= actId;
          continue;
        }
      }

      if (false && sys.auxVblCk()) {
        if (!WeakConvergenceCk(sys, this->hiXnRel - actPF, this->backReachPF)) {
          reqAdds |= actId;
          continue;
        }
      }
    }
  }

  PF delActPF( false );
  for (it = dels.begin(); it != dels.end(); ++it) {
    uint actId = *it;
    Remove1(this->candidates, actId);
    delActPF |= topo.actionPF(actId);
  }
  this->hiXnRel -= delActPF;

  bool revise = true;
  if (sys.auxVblCk()) {
    invariant = LegitInvariant(sys, this->loXnRel, this->hiXnRel);
    this->hi_invariant = invariant;
    if (invariant.tautologyCk(false)) {
      this->candidates.clear();
      this->loXnRel = false;
      this->hiXnRel = false;
      this->hiXnRel = false;
      return;
    }
    this->backReachPF =
      BackwardReachability(this->loXnRel, invariant, topo);

    for (uint i = 0; i < this->actions.size(); ++i) {
      uint actId = this->actions[i];
      if (this->inferredActions.elemCk(actId))  continue;
      if (!this->backReachPF.overlapCk(topo.actionPF(actId))) {
        this->candidates.clear();
        this->loXnRel = false;
        this->hiXnRel = false;
        this->hiXnRel = false;
        return;
      }
    }

    PF dl = (~invariant - topo.preimage(this->loXnRel));
    if (!dl.tautologyCk(false)) {
      this->deadlockPF |= dl;
      RankDeadlocksMCV(this->mcvDeadlocks,
                       sys.topology,
                       this->candidates,
                       this->deadlockPF);
      if (this->mcvDeadlocks.size() < 2) {
        return;
      }
      revise = false;
    }
  }
  if (revise) {
    ReviseDeadlocksMCV(this->mcvDeadlocks, topo, adds, dels);
  }

  for (it = adds.begin(); it != adds.end(); ++it) {
    uint actId = *it;
    if (this->bt_dbog) {
      DBogOF
        << " (lvl " << this->bt_level
        << ") (sz " << this->actions.size()
        << ") (rem " << this->candidates.size()
        << ")  ";
      OPut(DBogOF, topo.action(actId), topo) << '\n';
    }
  }

  reqAdds |= this->mcvDeadlocks[1].candidates;
  if (reqAdds.size() > this->mcvDeadlocks[1].candidates.size()) {
    DBog1( "did something: %u", (uint) (reqAdds.size() - this->mcvDeadlocks[1].candidates.size()));
  }
  if (!reqAdds.empty()) {
    this->inferredActions |= reqAdds;
    this->reviseActions(sys, reqAdds, Set<uint>());
  }
}

/**
 * Add convergence to a system.
 * The system will therefore be self-stabilizing.
 * This is the recursive function.
 *
 * \param sys  System definition. It is modified if convergence is added.
 * \return  True iff convergence could be added.
 */
  bool
AddConvergence(vector<uint>& retActions,
               const XnSys& sys,
               FMem_AddConvergence& tape,
               const AddConvergenceOpt& opt)
{
  while (!tape.candidates.empty()) {
    if (!sys.auxVblCk()) {
      if (!WeakConvergenceCk(sys, tape.hiXnRel, sys.invariant)) {
        return false;
      }
    }
    else {
      if (!WeakConvergenceCk(sys, tape.hiXnRel, tape.hi_invariant)) {
        return false;
      }
    }

    // Pick the action.
    uint actId = 0;
    if (!PickActionMCV(actId, sys, tape, opt)) {
      return false;
    }

    FMem_AddConvergence next( tape );
    next.bt_dbog = (tape.bt_dbog && (true || tape.bt_level < 18));
    next.bt_level = tape.bt_level + 1;
    next.reviseActions(sys, Set<uint>(actId), Set<uint>());

    bool found = AddConvergence(retActions, sys, next, opt);
    if (found) {
      return true;
    }
    tape.reviseActions(sys, Set<uint>(), Set<uint>(actId));
  }

  if (tape.deadlockPF.tautologyCk(false)) {
    const PF& invariant = sys.auxVblCk() ? tape.hi_invariant : sys.invariant;
    if (CycleCk(sys.topology, tape.loXnRel, ~invariant)) {
      DBog0( "Why are there cycles?" );
      return false;
    }
    if (!WeakConvergenceCk(sys, tape.loXnRel, invariant)) {
      DBog0( "Why does weak convergence not hold?" );
      return false;
    }
    retActions = tape.actions;
    return true;
  }
  return false;
}

/**
 * Add convergence to a system.
 * The system will therefore be self-stabilizing.
 *
 * \param sys  System definition. It is modified if convergence is added.
 * \return  True iff convergence could be added.
 */
  bool
AddConvergence(XnSys& sys, const AddConvergenceOpt& opt)
{
  XnNet& topo = sys.topology;
  const uint nPossibleActs = topo.nPossibleActs();

  if (sys.liveLegit && !sys.synLegit) {
    DBog0( "For liveness in the invariant, we must be able to add actions there!" );
    return false;
  }

  FMem_AddConvergence tape;
  tape.loXnRel = false;
  tape.hiXnRel = false;

  if (sys.invariant.tautologyCk(false)) {
    DBog0( "Invariant is empty!" );
    return false;
  }

  if (sys.invariant.tautologyCk(true)) {
    DBog0( "All states are invariant!" );
    if (!sys.auxVblCk()) {
      return true;
    }
  }

  for (uint i = 0; i < nPossibleActs; ++i) {
    bool add = true;

    XnAct act( topo.action(i) );
    const PF& actPF = topo.actionPF(i);

    // Check for self-loops.
    if (add) {
      const XnPc& pc = topo.pcs[act.pcIdx];
      bool selfloop = true;
      for (uint j = 0; j < pc.wvbls.size(); ++j) {
        if (act.w1[j] != act.w0[j]) {
          selfloop = false;
        }
      }
      add = !selfloop;
      if (false && selfloop) {
        OPut((DBogOF << "Action " << i << " is a self-loop: "), act, topo) << '\n';
      }
    }

    if (add && !sys.auxVblCk() && sys.invariant.overlapCk(actPF)) {
      // This action does starts in the invariant.
      // If /!sys.synLegit/, we shouldn't add any actions
      // within the legitimate states, even if closure isn't broken.
      if (!sys.synLegit || (~sys.invariant).overlapCk(topo.image(actPF, sys.invariant))) {
        add = false;
        if (false) {
          OPut((DBogOF << "Action " << i << " breaks closure: "), act, topo) << '\n';
        }
      }
    }

    if (add) {
      tape.candidates.push_back(i);
      tape.hiXnRel |= topo.actionPF(i);
    }
  }

  if (sys.liveLegit) {
    tape.deadlockPF = true;
  }
  else {
    tape.deadlockPF = ~sys.invariant;
    if (sys.auxVblCk()) {
      tape.deadlockPF |= topo.preimage(sys.legit_protocol);
    }
  }
  tape.backReachPF = sys.invariant;

  RankDeadlocksMCV(tape.mcvDeadlocks,
                   sys.topology,
                   tape.candidates,
                   tape.deadlockPF);

  if (tape.mcvDeadlocks.size() < 2) {
    DBog0("Cannot resolve all deadlocks with known actions!");
    return false;
  }

  {
    const bool forcePrune = true;
    tape.bt_dbog = true;
    tape.reviseActions(sys, Set<uint>(sys.actions), Set<uint>(), forcePrune);
  }

  vector<uint> retActions;
  bool found = AddConvergence(retActions, sys, tape, opt);
  if (!found)  return false;

  sys.actions = retActions;
  return true;
}

/** Execute me now!*/
int main(int argc, char** argv)
{
  enum ProblemInstance {
    ThreeColoringRingInstance,
    TwoColoringRingInstance,
    MaximalMatchingInstance,
    SumNotTwoInstance,
    AgreementRingInstance,
    DijkstraTokenRingInstance,
    ThreeBitTokenRingInstance,
    TwoBitTokenSpingInstance,
    TestTokenRingInstance,
    NProblemInstances
  } problem = NProblemInstances;
  int argi = (init_sysCx (&argc, &argv), 1);
  uint npcs = 4;
  AddConvergenceOpt opt;
  const char* modelFilePath = 0;

  // Use to disable picking only actions which resolve deadlocks
  // by making them backwards reachable from the invariant.
  //opt.pickBackReach = false;
  // Use to disable process ordering.
  //opt.nicePolicy = opt.NilNice;
  // Use to change picking method.
  //opt.pickMethod = opt.QuickPick;
  //opt.pickMethod = opt.LCVHeavyPick;
  opt.pickMethod = opt.LCVLitePick;

  if (argi < argc) {
    if (string(argv[argi]) == "-model") {
      ++argi;
      modelFilePath = argv[argi++];
      if (!modelFilePath){
        DBog0("No path given!!!!");
      }
    }

    if (string(argv[argi]) == "test") {
      DBog0( "Running tests..." );
      Test();
      DBog0( "Done." );
      lose_sysCx ();
      return 0;
    }
    else if (string(argv[argi]) == "3-coloring") {
      DBog0("Problem: 3-Coloring on Bidirectional Ring");
      problem = ThreeColoringRingInstance;
    }
    else if (string(argv[argi]) == "2-coloring") {
      DBog0("Problem: 2-Coloring on Unidirectional Ring");
      problem = TwoColoringRingInstance;
    }
    else if (string(argv[argi]) == "matching") {
      DBog0("Problem: Maximal Matching");
      problem = MaximalMatchingInstance;
    }
    else if (string(argv[argi]) == "sum-not-2") {
      DBog0("Problem: Sum-Not-2");
      problem = SumNotTwoInstance;
    }
    else if (string(argv[argi]) == "agreement") {
      DBog0("Problem: Agreement");
      problem = AgreementRingInstance;
    }
    else if (string(argv[argi]) == "dijkstra-tr") {
      DBog0("Problem: Dijkstra's Token Ring");
      problem = DijkstraTokenRingInstance;
    }
    else if (string(argv[argi]) == "3-bit-tr") {
      DBog0("Problem: Gouda's Three Bit Token Ring");
      problem = ThreeBitTokenRingInstance;
    }
    else if (string(argv[argi]) == "2-bit-tr") {
      DBog0("Problem: Dijkstra's Two Bit Token Spring");
      problem = TwoBitTokenSpingInstance;
    }
    else if (string(argv[argi]) == "test-tr") {
      DBog0("Problem: Testing Token Ring");
      problem = TestTokenRingInstance;
    }
    else{
      //printf("%s: Only supported argument is \"test\".\n", argv[0]);
      failout_sysCx("No valid problem given.\n");
    }
    ++argi;
  }
  else {
    failout_sysCx("No valid problem given.\n");
  }

  if (argi < argc) {
    npcs = (uint) atoi(argv[argi++]);
  }
  else {
    DBog1("Using default process count: %u", npcs);
  }
  if (argi < argc) {
    failout_sysCx("Too many arguments!");
  }

  // Set up the chosen problem.
  XnSys sys;
  switch(problem){
    case ThreeColoringRingInstance:
      InstThreeColoringRing(sys, npcs);  break;
    case TwoColoringRingInstance:
      InstTwoColoringRing(sys, npcs);  break;
    case MaximalMatchingInstance:
      InstMatching(sys, npcs);  break;
    case SumNotTwoInstance:
      InstSumNot(sys, npcs, 3, 2);  break;
    case AgreementRingInstance:
      InstAgreementRing(sys, npcs);  break;
    case DijkstraTokenRingInstance:
      InstDijkstraTokenRing(sys, npcs);  break;
    case ThreeBitTokenRingInstance:
      InstThreeBitTokenRing(sys, npcs);  break;
    case TwoBitTokenSpingInstance:
      InstTwoBitTokenSpring(sys, npcs);  break;
    case TestTokenRingInstance:
      InstTestTokenRing(sys, npcs);  break;
    case NProblemInstances:
    default:
      DBog0("No case for this problem instance!");
      return 1;
  }

  if (!sys.integrityCk()) {
    failout_sysCx ("Bad system definition.");
  }

  // Run the algorithm.
  bool found = AddConvergence(sys, opt);
  if (found) {
    DBog0("Solution found!");
    for (uint i = 0; i < sys.actions.size(); ++i) {
      const XnNet& topo = sys.topology;
      OPut(DBogOF, topo.action(sys.actions[i]), topo) << '\n';
    }
    if (modelFilePath)  {
      std::fstream of("model.pml",
                      std::ios::binary |
                      std::ios::out |
                      std::ios::trunc);
      OPutPromelaModel(of, sys);
      of.close();
      DBog1("Model written to \"%s\".", modelFilePath);
    }
  }
  else {
    DBog0("No solution found...");
  }
  std::flush(DBogOF);

  lose_sysCx ();
  return 0;
}

