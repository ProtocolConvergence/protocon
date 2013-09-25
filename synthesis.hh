
#ifndef PartialSynthesis_HH_
#define PartialSynthesis_HH_

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

class SynthesisCtx;
class PartialSynthesis;

static const bool DBog_RankDeadlocksMCV = false;

class DeadlockConstraint {
public:
  Cx::PFmla deadlockPF;
  Set<uint> candidates;
public:
  explicit DeadlockConstraint(const Cx::PFmla& _deadlockPF) :
    deadlockPF(_deadlockPF)
  {}
};

class AddConvergenceOpt {
public:
  enum PickActionHeuristic {
    MCVLitePick,
    GreedyPick,
    GreedySlowPick,
    LCVLitePick,
    LCVHeavyPick,
    LCVJankPick,
    QuickPick,
    RandomPick,
    ConflictPick,
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

  PickActionHeuristic pick_method;
  SearchMethod search_method;
  NicePolicy nicePolicy;
  bool pick_back_reach;
  Cx::OFile* log;
  bool verify_found;

  // For parallel algorithms.
  bool random_one_shot;
  uint max_depth;
  uint max_height;
  uint sys_pcidx;
  uint sys_npcs;
  uint ntrials;
  bool try_all;
  uint max_conflict_sz;
  const char* conflicts_xfilename;
  const char* conflicts_ofilename;
  bool snapshot_conflicts;

  AddConvergenceOpt() :
    pick_method( MCVLitePick )
    , search_method( BacktrackSearch )
    , nicePolicy( NilNice )
    , pick_back_reach( false )
    , log( &DBogOF )
    , verify_found( true )
    , random_one_shot( false )
    , max_depth( 0 )
    , max_height( 3 )
    , sys_pcidx( 0 )
    , sys_npcs( 1 )
    , ntrials( 0 )
    , try_all( false )
    , max_conflict_sz( 0 )
    , conflicts_xfilename( 0 )
    , conflicts_ofilename( 0 )
    , snapshot_conflicts( false )
  {}
};

// Decision level for synthesis.
class PartialSynthesis {
public:
  SynthesisCtx* ctx;

  Cx::OFile* log;
  uint bt_level;
  uint failed_bt_level;
  bool directly_add_conflicts;
  bool noconflicts;

  vector<uint> actions; ///< Chosen actions.
  Cx::Table<uint> picks; ///< Chosen actions, no inferred ones.
  vector<uint> candidates; ///< Candidate actions.
  vector<uint> noneeds; ///< Not needed because it doesn't resolve any potential deadlocks.
  Cx::PFmla deadlockPF; ///< Current deadlocks.
  Cx::PFmla lo_xn; ///< Under-approximation of the transition function.
  Cx::PFmla hi_xn; ///< Over-approximation of the transition function.
  Cx::PFmla hi_invariant;

  Cx::PFmla csp_pfmla;

public:
  explicit PartialSynthesis(SynthesisCtx* _ctx) :
    ctx( _ctx )
    , log( &Cx::OFile::null() )
    , bt_level( 0 )
    , failed_bt_level( 0 )
    , directly_add_conflicts( false )
    , noconflicts( false )
    , hi_invariant( false )
  {}

  /// Deadlocks ranked by how many candidate actions can resolve them.
  vector<DeadlockConstraint> mcvDeadlocks;

  uint add_small_conflict_set(const Xn::Sys& sys, const Cx::Table<uint>& delpicks);
  bool check_forward(const Xn::Sys& sys);
  bool revise_actions(const Xn::Sys& sys, Set<uint> adds, Set<uint> dels);
  bool pick_action(const Xn::Sys& sys, uint act_idx);
};

class SynthesisCtx {
public:
  PartialSynthesis base_inst;
  Cx::OFile* log;
  Cx::PFmlaCtx csp_pfmla_ctx;
  Cx::PFmla csp_base_pfmla;
  Cx::URandom urandom;
  AddConvergenceOpt opt;
  volatile bool* done;
  ConflictFamily conflicts;
  Cx::Table<Xn::Sys*> many_systems;

  SynthesisCtx()
    : base_inst( this )
    , log( &Cx::OFile::null() )
    , csp_base_pfmla(true)
    , done(0)
  {}
  SynthesisCtx(uint pcidx, uint npcs)
    : base_inst( this )
    , log( &Cx::OFile::null() )
    , csp_base_pfmla(true)
    , urandom(pcidx, npcs)
    , done(0)
  {}
  bool init(const Xn::Sys& sys, const AddConvergenceOpt& opt);
};


bool
candidate_actions(vector<uint>& candidates, const Xn::Sys& sys);
bool
coexist_ck(const Xn::ActSymm& a, const Xn::ActSymm& b);
void
RankDeadlocksMCV(vector<DeadlockConstraint>& dlsets,
                 const Xn::Net& topo,
                 const vector<uint>& actions,
                 const Cx::PFmla& deadlockPF);
bool
PickActionMCV(uint& ret_actId,
              const Xn::Sys& sys,
              const PartialSynthesis& tape,
              const AddConvergenceOpt& opt);

#endif

