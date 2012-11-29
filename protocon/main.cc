
#include "pf.hh"
#include "set.hh"
#include "xnsys.hh"

static std::ostream& DBogOF = std::cerr;

static const bool DBog_PruneCycles = false;
static const bool DBog_RankDeadlocksMRV = false;
static const bool DBog_PickActionMRV = false;

ostream& OPut(ostream& of, const XnAct& act, const XnNet& topo)
{
  const XnPc& pc = topo.pcs[act.pcIdx];
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    if (i != 0)  of << " && ";
    of << topo.wvbl(act.pcIdx, i).name << "==" << act.w0[i];
  }
  for (uint i = 0; i < pc.rvbls.size(); ++i) {
    of << " && ";
    of << topo.rvbl(act.pcIdx, i).name << "==" << act.r0[i];
  }
  of << " -->";
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    of << ' ' << topo.wvbl(act.pcIdx, i).name << ":=" << act.w1[i] << ';';
  }
  return of;
}

bool ConvergenceCk(const XnSys& sys, const PF& xnRel)
{
  PF span0( sys.invariant );

  const XnNet& topo = sys.topology;
  while (!span0.tautologyCk(true)) {
    PF span1( span0 | topo.preimage(xnRel, span0) );
    if (span1.equivCk(span0))  return false;
    span0 = span1;
  }
  return true;
}

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

  bool
PickActionMRV(uint& ret_actId,
              const vector<DeadlockConstraint>& dlsets,
              const XnNet& topo,
              const PF& backReachPF)
{
  for (uint i = 0; i < dlsets.size(); ++i) {
    const Set<uint>& candidates = dlsets[i].candidates;
    Set<uint>::const_iterator it;
    for (it = candidates.begin(); it != candidates.end(); ++it) {
      uint actId = *it;
      if (backReachPF.overlapCk(topo.image(topo.actionPF(actId)))) {
        ret_actId = actId;
        //if (true && candidates.begin() != it) {
        //  DBog0("Oh, this actually makes a difference!");
        //}
        return true;
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
  return false;
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
    bool add = false;
    if (!(tape.deadlockPF & actPF).tautologyCk(false)) {
      add = true;
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
    }
  }
  ReviseDeadlocksMRV(tape.mrvDeadlocks, topo, Set<uint>(), pruned);
  if (DBog_PruneCycles) {
    if (pruned.size() > 0) {
      DBog1("Pruned: %u", (uint) pruned.size());
    }
  }
}

  bool
AddConvergence(vector<uint> retActions,
               const XnSys& sys,
               FMem_AddConvergence& tape)
{
  PruneCycles(sys, tape);

  const XnNet& topo = sys.topology;
  while (!tape.candidates.empty()) {

    if (!ConvergenceCk(sys, tape.hiXnRel)) {
      return false;
    }
    if (tape.actions.size() < 18) {
      DBog2( "Level: %u  Remaining: %u",
             (uint) tape.actions.size(),
             (uint) tape.candidates.size() );
    }

#if 0
    uint actId = Pop1(tape.candidates);
#else
    uint actId = 0;
    if (!PickActionMRV(actId, tape.mrvDeadlocks, topo, tape.backReachPF)) {
      return false;
    }
    Remove1(tape.candidates, actId);
#endif
    FMem_AddConvergence next( tape );
    ReviseDeadlocksMRV(tape.mrvDeadlocks, topo, Set<uint>(), Set<uint>(actId));
    ReviseDeadlocksMRV(next.mrvDeadlocks, topo, Set<uint>(actId), Set<uint>());
    next.actions.push_back(actId);

    PF actPF = topo.actionPF(actId);
    next.loXnRel |= actPF;
    next.backReachPF =
      BackwardReachability(next.loXnRel, next.backReachPF, topo);

    PF resolved( topo.preimage(actPF) & tape.deadlockPF );
    next.deadlockPF -= resolved;

    bool found = AddConvergence(retActions, sys, next);
    if (found) {
      retActions.push_back(actId);
      return true;
    }

    tape.hiXnRel -= actPF;
  }
  return false;
}

  bool
AddConvergence(XnSys& sys)
{
  XnNet& topo = sys.topology;
  const uint nPossibleActs = topo.nPossibleActs();

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

    // Check for self-loops. This is an inefficient method,
    // but the check only happens once.
    if (add && (topo.preimage(actPF).equivCk(topo.image(actPF)))) {
      add = false;
      if (false) {
        OPut((DBogOF << "Action " << i << " is a self-loop: "), act, topo) << '\n';
      }
    }

    // This action does not start in the invariant.
    if (add && !(sys.invariant & topo.preimage(actPF)).tautologyCk(false)) {
      add = false;
      if (false) {
        OPut((DBogOF << "Action " << i << " breaks closure: "), act, topo) << '\n';
      }
    }

    if (add) {
      tape.candidates.push_back(i);
      tape.hiXnRel |= topo.actionPF(i);
    }
  }

  tape.deadlockPF = ~sys.invariant;
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

void BidirectionalRing(XnNet& topo, uint npcs, uint domsz)
{
  // Build a bidirectional ring where each process P_i
  // has variable m_i of domain size 3.
  for (uint i = 0; i < npcs; ++i) {
    char name[10];
    sprintf(name, "m%u", i);

    XnPc& pc = Grow1(topo.pcs);
    pc.addVbl(XnVbl(name, domsz));
    pc.addPriv((i+npcs-1) % npcs, 0);
    pc.addPriv((i+1) % npcs, 0);
  }
}

/**
 * Performs the 3 color on a ring problem.  Each process must be assigned
 * a color such that it'd color is not the same as either of its
 * neighbors.  The domain is [0,2], corresponding to each of 3 arbitrary
 * colors.
 *
 * \param sys  The system context
 * \param npcs The number of processes
 */
void ColorRing(XnSys& sys, uint npcs)
{
  // Initializes the system as a bidirectional ring with a 3 value domain
  // and the topology defined in sys
  XnNet& topo=sys.topology;
  BidirectionalRing(topo,npcs,3);

  // Commit to using this topology, and initilize MDD stuff
  topo.commitInitialization();
  sys.invariant=true;

  for(uint pcidx=0; pcidx<npcs; pcidx++){

    // mq is the current process, mp is the left process,
    // and mr is the right process.
    const PFVbl mp=topo.pfVblR(pcidx,0);
    const PFVbl mq=topo.pfVbl (pcidx,0);
    const PFVbl mr=topo.pfVblR(pcidx,1);

    // Add to the accepting states all of the states where
    // mq is a different color than both mp and mr
    sys.invariant &=
      (mp==0 && mq==1 && mr==2) ||
      (mp==0 && mq==2 && mr==1) ||
      (mp==1 && mq==2 && mr==0) ||
      (mq==1 && mq==0 && mr==2) ||
      (mp==2 && mq==0 && mr==1) ||
      (mp==2 && mq==1 && mr==0);
  }
}

void TokenRing(XnSys& sys, uint npcs)
{
}

void InstMatching(XnSys& sys, uint npcs)
{
  XnNet& topo = sys.topology;
  BidirectionalRing(topo, npcs, 3);

  // Commit to using this topology.
  // MDD stuff is initialized.
  topo.commitInitialization();
  sys.invariant = true;

  for (uint pcidx = 0; pcidx < npcs; ++pcidx) {
    const PFVbl mp = topo.pfVblR(pcidx, 0);
    const PFVbl mq = topo.pfVbl (pcidx, 0);
    const PFVbl mr = topo.pfVblR(pcidx, 1);

    // 0 = Self, 1 = Left, 2 = Right
    sys.invariant &=
      (mp == 1 && mq == 0 && mr == 2) || // ( left,  self, right)
      (mp == 2 && mq == 1           ) || // (right,  left,     X)
      (           mq == 2 && mr == 1);   // (    X, right,  left)
  }
}

void test()
{
  XnSys sys;
  InstMatching(sys, 3);

  XnNet& topo = sys.topology;

  Claim( topo.pcs[1].actUnchanged <= (topo.pfVbl(0, 0) == topo.pfVblPrimed(0, 0)) );
  Claim( topo.pcs[1].actUnchanged <= (topo.pfVbl(2, 0) == topo.pfVblPrimed(2, 0)) );

  XnAct act;
  act.pcIdx = 1;
  act.r0[0] = 1; // Left.
  act.r0[1] = 2; // Right.
  act.w0[0] = 2; // Right.
  act.w1[0] = 0; // Self.

  uint actId = topo.actionIndex(act);
  {
    XnAct action = topo.action(actId);
    Claim2_uint( act.pcIdx ,==, action.pcIdx );
    Claim2_uint( act.r0[0] ,==, action.r0[0] );
    Claim2_uint( act.r0[1] ,==, action.r0[1] );
    Claim2_uint( act.w0[0] ,==, action.w0[0] );
    Claim2_uint( act.w1[0] ,==, action.w1[0] );
  }

  PF actPF =
    topo.pcs[1].actUnchanged &
    ((topo.pfVblR     (1, 0) == 1) &
     (topo.pfVblR     (1, 1) == 2) &
     (topo.pfVbl      (1, 0) == 2) &
     (topo.pfVblPrimed(1, 0) == 0));
  Claim( !actPF.tautologyCk(false) );
  Claim( actPF.equivCk(topo.actionPF(actId)) );

  actPF =
    topo.pcs[1].actUnchanged &
    ((topo.pfVbl      (0, 0) == 1) &
     (topo.pfVbl      (2, 0) == 2) &
     (topo.pfVbl      (1, 0) == 2) &
     (topo.pfVblPrimed(1, 0) == 0));
  Claim( actPF.equivCk(topo.actionPF(actId)) );

  PF srcPF =
    ((topo.pfVblR(1, 0) == 1) &
     (topo.pfVblR(1, 1) == 2) &
     (topo.pfVbl (1, 0) == 2));
  PF dstPF =
    ((topo.pfVblR(1, 0) == 1) &
     (topo.pfVblR(1, 1) == 2) &
     (topo.pfVbl (1, 0) == 0));
  Claim( (actPF - srcPF).tautologyCk(false) );

  Claim( (dstPF & srcPF).tautologyCk(false) );

  {
    Claim( dstPF.equivCk(topo.image(actPF, srcPF)) );
    // The rest of this block is actually implied by the first check.
    Claim( dstPF <= topo.image(actPF, srcPF) );
    Claim( topo.image(actPF, srcPF) <= dstPF );
    Claim( topo.image(actPF, srcPF) <= (topo.pfVblR(1, 0) == 1) );
    Claim( topo.image(actPF, srcPF) <= (topo.pfVblR(1, 1) == 2) );
    Claim( topo.image(actPF, srcPF) <= (topo.pfVbl (1, 0) == 0) );
  }
  Claim( dstPF.equivCk(topo.image(actPF & srcPF)) );
  Claim( srcPF.equivCk(topo.preimage(actPF, dstPF)) );

  Claim( (sys.invariant - sys.invariant).tautologyCk(false) );
  Claim( (sys.invariant | ~sys.invariant).tautologyCk(true) );
  Claim( (srcPF & sys.invariant).tautologyCk(false) );
  Claim( !(dstPF & sys.invariant).tautologyCk(false) );
  Claim( !(~(dstPF & sys.invariant)).tautologyCk(true) );
  Claim( (actPF - srcPF).tautologyCk(false) );
}

int main(int argc, char** argv)
{
  int argi = 1;
  const uint NPs = 6;
  int problem;

  if (argi < argc) {
    if (string(argv[argi]) == "test") {
      DBog0( "Running tests..." );
      test();
      DBog0( "Done." );
      return 0;
    }
    else if(string(argv[argi])=="color"){
      DBog0("Problem: 3 Color Ring");
      problem=0;
    }
    else if(string(argv[argi])=="matching"){
      DBog0("Problem: Maximal Matching");
      problem=1;
    }
    else if(string(argv[argi])=="token"){
      DBog0("Problem: Dijkstra's Token Ring");
      problem=2;
      return 0;
    }
    else{
      //printf("%s: Only supported argument is \"test\".\n", argv[0]);
      printf("No valid problem given.\n");
     return 1;
    }
  }
  else{
    printf("No valid problem given.\n");
    return 1;
  }

#if 1
  XnSys sys;
  XnNet& topo = sys.topology;
  switch(problem){
    case 0: ColorRing(sys,NPs); break;
    case 1: InstMatching(sys,NPs); break;
    case 2: TokenRing(sys,NPs); break;
  }
  bool found = AddConvergence(sys);
  if (found) {
    DBog0("Solution found!");
  }
  else {
    DBog0("No solution found...");
  }

  DBog0("Showing all variables");
  print_mvar_list(topo.pfCtx.mdd_ctx());

  PFCtx& ctx = topo.pfCtx;

  //   m0==0 && (m1==0 || m1==2) && m2==1 --> m1:=1
  //   m0==0 && (m1==0 || m1==2) && m2==1 && m1'==1
  PF pf =
    topo.pcs[1].actUnchanged &&
    (topo.pfVbl(0, 0) == 0 &&
     (topo.pfVbl(1, 0) == 0 || topo.pfVbl(1, 0) == 2) &&
     topo.pfVbl(2, 0) == 0 &&
     topo.pfVblPrimed(1, 0) == 1);

  // Build an array of variable indices to see (m_0, m_0', m_1, m_1', m_2, m_2').
  array_t* vars = array_alloc(uint, 0);
  array_insert_last(uint, vars, topo.pfVbl      (0, 0).idx); // m_0
  array_insert_last(uint, vars, topo.pfVblPrimed(0, 0).idx); // m_0'
  array_insert_last(uint, vars, topo.pfVbl      (1, 0).idx); // m_1
  array_insert_last(uint, vars, topo.pfVblPrimed(1, 0).idx); // m_1'
  array_insert_last(uint, vars, topo.pfVbl      (2, 0).idx); // m_2
  array_insert_last(uint, vars, topo.pfVblPrimed(2, 0).idx); // m_2'

  mdd_gen* gen;
  array_t* minterm;
  // Show all satisfying valuations of the variables for the formula stored in /acts/
  DBog0("Showing satisfying valuations on m_0, m_0', m_1, m_1', m_2, m_2' of /acts/");
  mdd_t* acts = pf.dup_mdd();
  foreach_mdd_minterm(acts, gen, minterm, vars) {
    for (uint i = 0; i < (uint) minterm->num; ++i) {
      uint x = array_fetch(uint, minterm, i);
      uint vidx = array_fetch(uint, vars, i);
      fprintf(stdout, " %s=%u", ctx.vbl(vidx).name.c_str(), x);
    }
    fputc('\n', stdout);
    array_free(minterm);
  }
  mdd_free(acts);
  array_free(vars);
#endif

  return 0;
}

