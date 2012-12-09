
#include "pf.hh"
#include "set.hh"
#include "xnsys.hh"

static std::ostream& DBogOF = std::cerr;

static const bool DBog_PruneCycles = false;
static const bool DBog_RankDeadlocksMRV = false;
static const bool DBog_PickActionMRV = false;

/**
 * Output an action in a valid Promela format.
 */
  ostream&
OPut(ostream& of, const XnAct& act, const XnNet& topo)
{
  const XnPc& pc = topo.pcs[act.pcIdx];
  of << "/*P" << act.pcIdx << "*/ ";
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    if (i != 0)  of << " && ";
    of << topo.wvbl(act.pcIdx, i).name << "==" << act.w0[i];
  }
  for (uint i = 0; i < pc.rvbls.size(); ++i) {
    of << " && ";
    of << topo.rvbl(act.pcIdx, i).name << "==" << act.r0[i];
  }
  of << " ->";
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    of << ' ' << topo.wvbl(act.pcIdx, i).name << "=" << act.w1[i] << ';';
  }
  return of;
}

/**
 * Check for weak convergence to the invariant.
 */
  bool
WeakConvergenceCk(const XnSys& sys, const PF& xnRel)
{
  const XnNet& topo = sys.topology;
  if (sys.liveLegit && !(sys.invariant <= topo.preimage(xnRel))) {
    return false;
  }
  PF span0( sys.invariant );
  while (!span0.tautologyCk(true)) {
    PF span1( span0 | topo.preimage(xnRel, span0) );
    if (span1.equivCk(span0))  return false;
    span0 = span1;
  }
  return true;
}

/**
 * Check for cycles outside of the invariant.
 */
bool CycleCk(const XnSys& sys, const PF& xnRel)
{
  PF span0( ~sys.invariant );

  const XnNet& topo = sys.topology;
  while (true) {
    PF span1( span0 );
    //span0 -= span0 - sys.image(xnRel, span0);
    span0 &= topo.preimage(xnRel, span0);

    if (span0.equivCk(span1))  break;
  }

  return !span0.tautologyCk(false);
}

/**
 * Perform backwards reachability.
 * \param xnRel  Transition function.
 * \param pf  Initial states.
 * \param topo  Topology of the system.
 */
  PF
BackwardReachability(const PF& xnRel, const PF& pf, const XnNet& topo)
{
  PF visitPF( pf );
  PF layerPF( topo.preimage(xnRel, pf) - visitPF );
  while (!layerPF.tautologyCk(false)) {
    visitPF |= layerPF;
    layerPF = topo.preimage(xnRel, layerPF) - visitPF;
  }
  return visitPF;
}

class DeadlockConstraint {
public:
  PF deadlockPF;
  Set<uint> candidates;
public:
  explicit DeadlockConstraint(const PF& _deadlockPF) :
    deadlockPF(_deadlockPF)
  {}
};

class FMem_AddConvergence {
public:
  PF deadlockPF; ///< Current deadlocks.
  PF loXnRel; ///< Under-approximation of the transition function.
  PF hiXnRel; ///< Over-approximation of the transition function.
  PF backReachPF; ///< Backwards reachable from invariant.
  vector<uint> actions; ///< Chosen actions.
  vector<uint> candidates; ///< Candidate actions.

  /// Deadlocks ranked by how many candidate actions can resolve them.
  vector<DeadlockConstraint> mrvDeadlocks;
};

/** Rank the deadlocks by how many actions can resolve them.*/
  void
RankDeadlocksMRV(vector<DeadlockConstraint>& dlsets,
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

  if (DBog_RankDeadlocksMRV) {
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
ReviseDeadlocksMRV(vector<DeadlockConstraint>& dlsets,
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

    uint prevSize = candidates1.size();
    candidates1 -= addCandidates;
    bool changed = (prevSize != candidates1.size());
    if (changed) {
      PF diffDeadlockPF = deadlockPF1 & addGuardPF;
      deadlockPF1 -= diffDeadlockPF;
      Set<uint> diffCandidates1; // To remove from this rank.
      Set<uint>::iterator it;
      for (it = candidates1.begin(); it != candidates1.end(); ++it) {
        uint actId = *it;
        PF candidateGuardPF = topo.actionPF(actId);
        if ((deadlockPF1 & candidateGuardPF).tautologyCk(false)) {
          // Action no longer resolves any deadlocks in this rank.
          diffCandidates1 |= actId;
        }
      }
      candidates1 -= diffCandidates1;
    }

    prevSize = candidates1.size();
    candidates1 -= delCandidates;
    changed = (prevSize != candidates1.size());
    if (changed) {
      Set<uint>& candidates0 = dlsets[i-1].candidates;
      PF& deadlockPF0 = dlsets[i-1].deadlockPF;
      PF diffDeadlockPF = deadlockPF1 & delGuardPF;
      deadlockPF1 -= diffDeadlockPF;
      deadlockPF0 |= diffDeadlockPF;

      Set<uint> diffCandidates0; // To add to previous rank.
      Set<uint> diffCandidates1; // To remove from this rank.
      Set<uint>::iterator it;
      for (it = candidates1.begin(); it != candidates1.end(); ++it) {
        uint actId = *it;
        PF candidateGuardPF = topo.actionPF(actId);
        if (!(diffDeadlockPF & candidateGuardPF).tautologyCk(false)) {
          // Action resolves deadlocks in previous rank.
          diffCandidates0 |= actId;
          if ((deadlockPF1 & candidateGuardPF).tautologyCk(false)) {
            // Action no longer resolves any deadlocks in this rank.
            diffCandidates1 |= actId;
          }
        }
      }
      candidates0 |= diffCandidates0;
      candidates1 -= diffCandidates1;
    }
  }
}

/**
 * Pick the next candidate action to use.
 * The minimum remaining values (MRV) heuristic may be used.
 *
 * \param ret_actId  Return value. Action to use.
 * \param dlsets  Deadlock sets ordered by number of
 *   resolving candidate actions.
 * \param backReachPF  Backwards reachability from invariant.
 * \return True iff an action was picked. It should return
 *   true unless you're doing it wrong).
 */
  bool
PickActionMRV(uint& ret_actId,
              const vector<DeadlockConstraint>& dlsets,
              const XnNet& topo,
              const PF& backReachPF,
              const map<uint,uint>& conflicts)
{
  if (false) {
    //(void) conflicts;
    // This block picks the action which resolves the most deadlocks.
    // The number of resolved deadlocks is computed by the deadlock sets.
    map< uint, uint > resolveMap;
    for (uint i = 1; i < dlsets.size(); ++i) {
      const Set<uint>& candidates = dlsets[i].candidates;
      Set<uint>::const_iterator it;
      for (it = candidates.begin(); it != candidates.end(); ++it) {
        uint* n = MapLookup(resolveMap, *it);
        uint w = i-1;
        if (i == 1) {
          // We shall assert this action.
          w = dlsets.size() * dlsets.size() * dlsets.size();
        }
        if (!n) {
          resolveMap[*it] = w;
        }
        else {
          *n += w;
        }
      }
    }

    if (!resolveMap.empty()) {
      uint actId = 0;
      uint nMax = 0;
      map<uint,uint>::const_iterator it;
      for (it = resolveMap.begin(); it != resolveMap.end(); ++it) {
        uint n = it->second;
        if (backReachPF.overlapCk(topo.image(topo.actionPF(it->first)))) {
          if (!(topo.preimage(topo.actionPF(it->first)) <= backReachPF)) {
            n += dlsets.size() * dlsets.size();
          }
        }
        if (n > nMax) {
          actId = it->first;
          nMax = n;
        }
      }
      ret_actId = actId;
      return true;
    }
  }
  else if (true) {
    //(void) conflicts;
    // Do minimum remaining values (MRV).
    // That is, find an action which resolves a deadlock for which
    // can only be resolved by some small number of actions.
    // Try to choose an action which adds a new path to the invariant.
    for (uint i = 0; i < dlsets.size(); ++i) {
      const Set<uint>& candidates = dlsets[i].candidates;
      Set<uint>::const_iterator it;
      for (it = candidates.begin(); it != candidates.end(); ++it) {
        uint actId = *it;
        const PF actPF( topo.actionPF(actId) );
        if (backReachPF.overlapCk(topo.image(actPF))) {
          if (!(topo.preimage(actPF) <= backReachPF)) {
            ret_actId = actId;
            if (false && candidates.begin() != it) {
              DBog0("Oh, this actually makes a difference!");
            }
            return true;
          }
        }
      }

      if (!candidates.empty()) {
        uint actId = candidates.elem();
        if (DBog_PickActionMRV) {
          DBog1( "Picked at rank %u", i );
        }
        ret_actId = actId;
        return true;
      }
    }
  }
  else if (false) {
    //(void) backReachPF;
    // Do minimum remaining values (MRV) with least constraining value (LCV).
    for (uint i = 0; i < dlsets.size(); ++i) {
      const Set<uint>& candidates = dlsets[i].candidates;
      Set<uint>::const_iterator it;
      if (!candidates.empty()) {
        it = candidates.begin();
        uint actId = *it;

        bool maximize = false;
        bool have = false;
        uint nConflictsExtremum = 0;

        for (++it; it != candidates.end(); ++it) {
          uint nConflicts = *MapLookup(conflicts, *it);
          if (!have) {
            have = true;
            nConflictsExtremum = nConflicts;
            actId = *it;
          }
          else if (maximize && nConflicts > nConflictsExtremum) {
            nConflictsExtremum = nConflicts;
            actId = *it;
          }
          else if (!maximize && nConflicts < nConflictsExtremum) {
            nConflictsExtremum = nConflicts;
            actId = *it;
          }
        }

        ret_actId = actId;
        return true;
      }
    }
  }
  return false;
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

/** Perform forward checking.*/
  void
PruneCycles(const XnSys& sys, FMem_AddConvergence& tape)
{
  vector<uint> candidates = tape.candidates;
  tape.candidates.clear();
  Set<uint> pruned;

  const XnNet& topo = sys.topology;
  for (uint i = 0; i < candidates.size(); ++i) {
    uint actId = candidates[i];
    PF actPF( topo.actionPF(actId) );
    bool add = true;
    if (add && !tape.deadlockPF.overlapCk(topo.preimage(actPF))) {
      add = false;
    }
    if (add && CycleCk(sys, tape.loXnRel | actPF)) {
      add = false;
    }
    if (add) {
      tape.candidates.push_back(actId);
    }
    else {
      pruned |= actId;
      tape.hiXnRel -= actPF;
      //OPut( DBogOF << "Pruned: ", topo.action(actId), topo) << '\n';
    }
  }
  ReviseDeadlocksMRV(tape.mrvDeadlocks, topo, Set<uint>(), pruned);
  if (DBog_PruneCycles) {
    if (pruned.size() > 0) {
      DBog1("Pruned: %u", (uint) pruned.size());
    }
  }
}

/**
 * For each action, check to see if its inclusion will make the
 * solution impossible after one step of pruning.
 */
  map<uint,uint>
PruneCandidatesAC3(const XnSys& sys, FMem_AddConvergence& tape)
{
  const XnNet& topo = sys.topology;
  vector<uint>& candidates = tape.candidates;
  bool changed = true;
  map<uint,uint> conflicts;
  // Does this help when enforcing liveness in the invariant?
  //if (!(tape.deadlockPF <= sys.invariant)) {
  //  return conflicts;
  //}
  while (changed) {
    changed = false;
    conflicts.clear();
    for (uint i = 0; i < candidates.size();) {
      uint actId = candidates[i];

      FMem_AddConvergence tmptape(tape);
      PF actPF = topo.actionPF(actId);
      tmptape.loXnRel |= actPF;
      PruneCycles(sys, tmptape);
      {
        Set<uint> delSet;
        QuickTrim(delSet, tmptape.candidates, sys.topology, actId);
        Set<uint>::const_iterator delit;
        for (delit = delSet.begin(); delit != delSet.end(); ++delit) {
          tmptape.hiXnRel -= topo.actionPF(*delit);
          Remove1(tmptape.candidates, *delit);
        }
      }
      conflicts[actId] = candidates.size() - tmptape.candidates.size();
      bool prune = !WeakConvergenceCk(sys, tmptape.hiXnRel);

      if (!prune) {
        ++i;
      }
      else {
        DBog0("AC3 pruned something!");
        changed = true;
        tape.hiXnRel -= actPF;
        if (!WeakConvergenceCk(sys, tape.hiXnRel)) {
          return map<uint,uint>();
        }
        candidates.erase(candidates.begin() + i);
        ReviseDeadlocksMRV(tape.mrvDeadlocks, topo, Set<uint>(), Set<uint>(actId));
      }
    }
  }
  return conflicts;
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
               FMem_AddConvergence& tape)
{
  if (tape.deadlockPF.tautologyCk(false)) {
    return true;
  }
  PruneCycles(sys, tape);

  const XnNet& topo = sys.topology;
  while (!tape.candidates.empty()) {


    map<uint,uint> conflicts;
    if (false) {
      // AC3 is slooooww and doesn't help as implemented!
      // We already have forward checking, which does well.
      conflicts = PruneCandidatesAC3(sys, tape);
    }

    if (!WeakConvergenceCk(sys, tape.hiXnRel)) {
      return false;
    }

    // Pick the action.
    uint actId;
    if (true) {
      actId = 0;
      if (!PickActionMRV(actId, tape.mrvDeadlocks, topo, tape.backReachPF, conflicts)) {
        return false;
      }
      Remove1(tape.candidates, actId);
    }
    else if (false) {
      actId = Pop1(tape.candidates);
    }
    else if (false) {
      actId = tape.candidates[0];
      bool maximize = false;
      bool have = false;
      uint nConflictsExtremum = 0;
      for (uint i = 0; i < tape.candidates.size(); ++i) {
        uint nConflicts = *MapLookup(conflicts, tape.candidates[i]);
        if (!tape.backReachPF.overlapCk(topo.image(topo.actionPF(tape.candidates[i])))) {
          // Don't use
        }
        else if (!have) {
          have = true;
          nConflictsExtremum = nConflicts;
          actId = tape.candidates[i];
        }
        else if (maximize && nConflicts > nConflictsExtremum) {
          nConflictsExtremum = nConflicts;
          actId = tape.candidates[i];
        }
        else if (!maximize && nConflicts < nConflictsExtremum) {
          nConflictsExtremum = nConflicts;
          actId = tape.candidates[i];
        }
      }
      Remove1(tape.candidates, actId);
    }

    FMem_AddConvergence next( tape );
    ReviseDeadlocksMRV(tape.mrvDeadlocks, topo, Set<uint>(), Set<uint>(actId));
    next.actions.push_back(actId);

    PF actPF = topo.actionPF(actId);
    next.loXnRel |= actPF;
    next.backReachPF =
      BackwardReachability(next.loXnRel, next.backReachPF, topo);

    PF resolved( topo.preimage(actPF) & tape.deadlockPF );
    next.deadlockPF -= resolved;

    //if (true || tape.candidates.size() > 30) {
    if (true || tape.actions.size() < 18) {
      DBogOF << " -- " << tape.actions.size()
        << " -- " << tape.candidates.size() << " -- ";
      OPut(DBogOF, topo.action(actId), topo) << '\n';
    }

    {
      Set<uint> delSet;
      QuickTrim(delSet, next.candidates, sys.topology, actId);
      Set<uint>::const_iterator delit;
      for (delit = delSet.begin(); delit != delSet.end(); ++delit) {
        next.hiXnRel -= topo.actionPF(*delit);
        Remove1(next.candidates, *delit);
        //OPut( DBogOF << "Pruned: ", topo.action(*delit), topo) << '\n';
      }
      ReviseDeadlocksMRV(next.mrvDeadlocks, topo, Set<uint>(actId), delSet);
    }

    bool found = AddConvergence(retActions, sys, next);
    if (found) {
      retActions.push_back(actId);
      return true;
    }

    tape.hiXnRel -= actPF;
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
AddConvergence(XnSys& sys)
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
    return true;
  }

  for (uint i = 0; i < nPossibleActs; ++i) {
    bool add = true;

    XnAct act( topo.action(i) );
    PF actPF( topo.actionPF(i) );

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

    if (add && sys.invariant.overlapCk(topo.preimage(actPF))) {
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
  }
  tape.backReachPF = sys.invariant;

  RankDeadlocksMRV(tape.mrvDeadlocks,
                   sys.topology,
                   tape.candidates,
                   tape.deadlockPF);


  vector<uint> retActions;
  bool found = AddConvergence(retActions, sys, tape);
  if (!found)  return false;

  while (!retActions.empty()) {
    sys.actions.push_back(Pop1(retActions));
  }

  return true;
}

#include "inst.cc"
#include "test.cc"

/** Execute me now!*/
int main(int argc, char** argv)
{
  enum ProblemInstance {
    ThreeColoringInstance,
    MaximalMatchingInstance,
    DijkstraTokenRingInstance,
    ThreeBitTokenRingInstance,
    NProblemInstances
  } problem = NProblemInstances;
  int argi = 1;
  uint npcs = 4;

  if (argi < argc) {
    if (string(argv[argi]) == "test") {
      DBog0( "Running tests..." );
      Test();
      DBog0( "Done." );
      return 0;
    }
    else if(string(argv[argi])=="color"){
      DBog0("Problem: 3 Color Ring");
      problem = ThreeColoringInstance;
    }
    else if(string(argv[argi])=="matching"){
      DBog0("Problem: Maximal Matching");
      problem = MaximalMatchingInstance;
    }
    else if(string(argv[argi])=="dijkstra-tr"){
      DBog0("Problem: Dijkstra's Token Ring");
      problem = DijkstraTokenRingInstance;
    }
    else if(string(argv[argi])=="3-bit-tr"){
      DBog0("Problem: Dijkstra's Token Ring");
      problem = ThreeBitTokenRingInstance;
    }
    else{
      //printf("%s: Only supported argument is \"test\".\n", argv[0]);
      printf("No valid problem given.\n");
      return 1;
    }
    ++argi;
  }
  else {
    DBog0("No valid problem given.");
    return 1;
  }

  if (argi < argc) {
    npcs = (uint) atoi(argv[argi++]);
  }
  else {
    DBog1("Using default process count: %u", npcs);
  }
  if (argi < argc) {
    DBog0("Too many arguments!");
    return 1;
  }

  // Set up the chosen problem.
  XnSys sys;
  switch(problem){
    case ThreeColoringInstance:
      ColorRing(sys, npcs);  break;
    case MaximalMatchingInstance:
      InstMatching(sys, npcs);  break;
    case DijkstraTokenRingInstance:
      InstDijkstraTokenRing(sys, npcs);  break;
    case ThreeBitTokenRingInstance:
      InstThreeBitTokenRing(sys, npcs);  break;
    case NProblemInstances:
    default:
      DBog0("No case for this problem instance!");
      return 1;
  }

  // Run the algorithm.
  bool found = AddConvergence(sys);
  if (found) {
    DBog0("Solution found!");
    for (uint i = 0; i < sys.actions.size(); ++i) {
      const XnNet& topo = sys.topology;
      OPut(DBogOF, topo.action(sys.actions[i]), topo) << '\n';
    }
  }
  else {
    DBog0("No solution found...");
  }

  return 0;
}

