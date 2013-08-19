
#ifndef StabilitySynLvl_HH_
#define StabilitySynLvl_HH_

#include "cx/set.hh"
#include "cx/urandom.hh"
#include "pfmla.hh"
#include "inst.hh"
#include "promela.hh"
#include "test.hh"
#include "xnsys.hh"
#include <fstream>
#include "protoconfile.hh"

extern Cx::OFile DBogOF;

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
  bool bt_dbog;

  // For parallel algorithms.
  bool random_one_shot;
  uint bt_depth;
  uint sys_pcidx;
  uint sys_npcs;

  AddConvergenceOpt() :
    pickMethod( GreedyPick )
    , nicePolicy( EndNice )
    , pickBackReach( false )
    , bt_dbog( true )
    , random_one_shot( false )
    , bt_depth( 3 )
    , sys_pcidx( 0 )
    , sys_npcs( 1 )
  {}
};

class StabilitySyn {
public:
  Cx::PFmlaCtx csp_pfmla_ctx;
  Cx::PFmla csp_base_pfmla;
  Cx::URandom urandom;
  AddConvergenceOpt opt;
  volatile bool* solution_found;

  StabilitySyn()
    : csp_base_pfmla(true)
    , solution_found(0)
  {}
  StabilitySyn(uint pcidx, uint npcs)
    : csp_base_pfmla(true)
    , urandom(pcidx, npcs)
    , solution_found(0)
  {}
};

// Decision level for synthesis.
class StabilitySynLvl {
public:
  StabilitySyn* ctx;

  bool bt_dbog;
  uint bt_level;
  uint failed_bt_level;

  vector<uint> actions; ///< Chosen actions.
  vector<uint> candidates; ///< Candidate actions.
  Cx::Set<uint> conflict_set; ///< Conflict set for backjumping.
  PF deadlockPF; ///< Current deadlocks.
  PF loXnRel; ///< Under-approximation of the transition function.
  PF hiXnRel; ///< Over-approximation of the transition function.
  PF backReachPF; ///< Backwards reachable from invariant.
  PF hi_invariant;

  Cx::PFmla csp_pfmla;

public:
  StabilitySynLvl(StabilitySyn* _ctx) :
    ctx( _ctx )
    , bt_dbog( false )
    , bt_level( 0 )
    , failed_bt_level( 0 )
    , hi_invariant( false )
  {}

  /// Deadlocks ranked by how many candidate actions can resolve them.
  vector<DeadlockConstraint> mcvDeadlocks;

  bool check_forward(const Xn::Sys& sys);
  bool revise_actions(const Xn::Sys& sys, Set<uint> adds, Set<uint> dels);
};

bool
candidate_actions(vector<uint>& candidates, const Xn::Sys& sys);
bool
coexist_ck(const Xn::ActSymm& a, const Xn::ActSymm& b);
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

