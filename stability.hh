
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
#include "conflictfamily.hh"

class StabilitySyn;
class StabilitySynLvl;

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
  enum SearchMethod {
    BacktrackSearch,
    RankShuffleSearch,
    RandomBacktrackSearch,
    NSearchMethods
  };

  PickActionHeuristic pickMethod;
  SearchMethod search_method;
  NicePolicy nicePolicy;
  bool pickBackReach;
  bool bt_dbog;
  bool verify_found;

  // For parallel algorithms.
  bool random_one_shot;
  uint bt_depth;
  uint sys_pcidx;
  uint sys_npcs;
  uint ntrials;
  bool try_all;
  uint max_conflict_sz;
  const char* conflicts_xfilename;
  const char* conflicts_ofilename;
  bool snapshot_conflicts;

  AddConvergenceOpt() :
    pickMethod( GreedyPick )
    , search_method( BacktrackSearch )
    , nicePolicy( EndNice )
    , pickBackReach( false )
    , bt_dbog( true )
    , verify_found( true )
    , random_one_shot( false )
    , bt_depth( 3 )
    , sys_pcidx( 0 )
    , sys_npcs( 1 )
    , ntrials( 300 )
    , try_all( false )
    , max_conflict_sz( 0 )
    , conflicts_xfilename( 0 )
    , conflicts_ofilename( 0 )
    , snapshot_conflicts( false )
  {}
};

class StabilitySyn {
public:
  Cx::PFmlaCtx csp_pfmla_ctx;
  Cx::PFmla csp_base_pfmla;
  Cx::URandom urandom;
  AddConvergenceOpt opt;
  volatile bool* done;
  ConflictFamily conflicts;
  StabilitySynLvl* base_lvl;

  StabilitySyn()
    : csp_base_pfmla(true)
    , done(0)
  {}
  StabilitySyn(uint pcidx, uint npcs)
    : csp_base_pfmla(true)
    , urandom(pcidx, npcs)
    , done(0)
  {}
};

// Decision level for synthesis.
class StabilitySynLvl {
public:
  StabilitySyn* ctx;

  bool bt_dbog;
  uint bt_level;
  uint failed_bt_level;
  bool directly_add_conflicts;
  bool noconflicts;

  vector<uint> actions; ///< Chosen actions.
  Cx::Table<uint> picks; ///< Chosen actions, no inferred ones.
  vector<uint> candidates; ///< Candidate actions.
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
    , directly_add_conflicts( false )
    , noconflicts( false )
    , hi_invariant( false )
  {}

  /// Deadlocks ranked by how many candidate actions can resolve them.
  vector<DeadlockConstraint> mcvDeadlocks;

  void add_small_conflict_set(const Xn::Sys& sys, const Cx::Table<uint>& delpicks);
  bool check_forward(const Xn::Sys& sys);
  bool revise_actions(const Xn::Sys& sys, Set<uint> adds, Set<uint> dels);
  bool pick_action(const Xn::Sys& sys, uint act_idx);
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

