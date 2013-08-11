
#ifndef StabilitySynLvl_HH_
#define StabilitySynLvl_HH_

#include "cx/set.hh"
#include "pfmla.hh"
#include "inst.hh"
#include "promela.hh"
#include "test.hh"
#include "xnsys.hh"
#include <fstream>
#include "protoconfile.hh"
#include "ordersyn.hh"

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

// Decision level for synthesis.
class StabilitySynLvl {
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
  StabilitySynLvl() :
    bt_dbog( false )
    , bt_level( 0 )
    , hi_invariant( false )
  {}

  /// Deadlocks ranked by how many candidate actions can resolve them.
  vector<DeadlockConstraint> mcvDeadlocks;

  void reviseActions(const Xn::Sys& sys, Set<uint> adds, Set<uint> dels,
                     bool forcePrune=false);
};

void
RankDeadlocksMCV(vector<DeadlockConstraint>& dlsets,
                 const Xn::Net& topo,
                 const vector<uint>& actions,
                 const PF& deadlockPF);
bool
PickActionMCV(uint& ret_actId,
              const Xn::Sys& sys,
              const StabilitySynLvl& tape,
              const AddConvergenceOpt& opt);

#endif

