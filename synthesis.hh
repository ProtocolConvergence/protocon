
#ifndef PartialSynthesis_HH_
#define PartialSynthesis_HH_

#include "cx/set.hh"
#include "cx/urandom.hh"
#include "pfmla.hh"
#include "inst.hh"
#include "promela.hh"
#include "xnsys.hh"
#include <fstream>
#include "prot-xfile.hh"
#include "conflictfamily.hh"
#include "stabilization.hh"

class SynthesisCtx;
class PartialSynthesis;

static const bool DBog_RankDeadlocksMRV = false;

class DeadlockConstraint {
public:
  Cx::PFmla deadlockPF;
  Set<uint> candidates;
public:
  DeadlockConstraint() :
    deadlockPF(false)
  {}

  explicit DeadlockConstraint(const Cx::PFmla& _deadlockPF) :
    deadlockPF(_deadlockPF)
  {}
};

class AddConvergenceOpt {
public:
  enum PickActionHeuristic {
    MRVLitePick,
    GreedyPick,
    GreedySlowPick,
    LCVLitePick,
    LCVHeavyPick,
    LCVJankPick,
    QuickPick,
    FullyRandomPick,
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
    NSearchMethods
  };

  PickActionHeuristic pick_method;
  SearchMethod search_method;
  NicePolicy nicePolicy;
  bool pick_back_reach;
  Cx::OFile* log;
  bool verify_found;

  // For parallel algorithms.
  bool randomize_pick;
  bool system_urandom;
  uint max_depth;
  uint max_height;
  uint sys_pcidx;
  uint sys_npcs;
  uint ntrials;
  bool try_all;
  bool optimize_soln;
  uint max_conflict_sz;
  bool snapshot_conflicts;
  bool solution_as_conflict;
  vector<uint> known_solution;
  Cx::Table< vector<uint> > solution_guesses;
  Cx::String livelock_ofilepath;
  uint n_livelock_ofiles;

  AddConvergenceOpt() :
    pick_method( MRVLitePick )
    , search_method( BacktrackSearch )
    , nicePolicy( NilNice )
    , pick_back_reach( false )
    , log( &DBogOF )
    , verify_found( true )
    , randomize_pick( true )
    , system_urandom( false )
    , max_depth( 0 )
    , max_height( 3 )
    , sys_pcidx( 0 )
    , sys_npcs( 1 )
    , ntrials( 0 )
    , try_all( false )
    , optimize_soln( false )
    , max_conflict_sz( 0 )
    , snapshot_conflicts( false )
    , solution_as_conflict( false )
    , n_livelock_ofiles( 0 )
  {}
};

// Decision level for synthesis.
class PartialSynthesis {
public:
  SynthesisCtx* ctx;
  uint sys_idx;

  Cx::OFile* log;
  uint bt_level;
  uint failed_bt_level;
  bool directly_add_conflicts;
  bool no_conflict;
  bool no_partial;

  vector<uint> actions; ///< Chosen actions.
  Cx::Table<uint> picks; ///< Chosen actions, no inferred ones.
  vector<uint> candidates; ///< Candidate actions.
  Cx::PFmla deadlockPF; ///< Current deadlocks.
  Cx::PFmla lo_xn; ///< Under-approximation of the transition function.
  Cx::PFmla hi_xn; ///< Over-approximation of the transition function.
  Cx::PFmla hi_invariant;
  uint lo_nlayers;

  Cx::PFmla csp_pfmla;

  Cx::Table<PartialSynthesis> instances;  // Other instances of the parameterized system.

public:
  explicit PartialSynthesis(SynthesisCtx* _ctx, uint idx=0)
    : ctx( _ctx )
    , sys_idx( idx )
    , log( &Cx::OFile::null() )
    , bt_level( 0 )
    , failed_bt_level( 0 )
    , directly_add_conflicts( false )
    , no_conflict( false )
    , no_partial( false )
    , lo_xn( false )
    , hi_xn( false )
    , hi_invariant( false )
    , lo_nlayers( 1 )
  {}

  /// Deadlocks ranked by how many candidate actions can resolve them.
  vector<DeadlockConstraint> mcv_deadlocks;

  PartialSynthesis& operator[](uint i) {
    if (i == 0)  return *this;
    return this->instances[i-1];
  }

  const PartialSynthesis& operator[](uint i) const {
    if (i == 0)  return *this;
    return this->instances[i-1];
  }
  uint sz() const {
    return 1+instances.sz();
  }

  const StabilizationOpt& stabilization_opt() const;

  void godeeper1() {
    for (uint i = 0; i < this->sz(); ++i) {
      (*this)[i].bt_level += 1;
    }
  }

  bool candidates_ck() const {
    for (uint i = 0; i < this->sz(); ++i) {
      if ((*this)[i].no_partial)
        continue;
      if (!(*this)[i].candidates.empty())
        return true;
    }
    return false;
  }

  bool deadlocks_ck() const {
    for (uint i = 0; i < this->sz(); ++i) {
      if ((*this)[i].no_partial)
        continue;
      if ((*this)[i].deadlockPF.sat_ck())
        return true;
    }
    return false;
  }

  uint add_small_conflict_set(const Cx::Table<uint>& delpicks);
  bool check_forward(Set<uint>& adds, Set<uint>& dels, Set<uint>& rejs);
  bool revise_actions_alone(Set<uint>& adds, Set<uint>& dels, Set<uint>& rejs, uint* ret_nlayers = 0);
  bool revise_actions(const Set<uint>& adds, const Set<uint>& dels, uint* ret_nlayers = 0);
  bool pick_action(uint act_idx);
  bool pick_actions(const vector<uint>& act_idcs);
  bool pick_actions_separately(const vector<uint>& act_idcs);
};

class SynthesisCtx {
public:
  PartialSynthesis base_partial;
  Cx::Table<const Xn::Sys*> systems;
  Cx::OFile* log;
  Cx::PFmlaCtx csp_pfmla_ctx;
  Cx::PFmla csp_base_pfmla;
  Cx::URandom urandom;
  AddConvergenceOpt opt;
  Cx::Table<StabilizationOpt> stabilization_opts;
  uint optimal_nlayers_sum;
  Bool (*done_ck_fn) (void*);
  void* done_ck_mem;
  ConflictFamily conflicts;

  SynthesisCtx()
    : base_partial( this )
    , log( &Cx::OFile::null() )
    , csp_base_pfmla(true)
    , done_ck_fn(0)
    , done_ck_mem(0)
  {}
  SynthesisCtx(uint pcidx, uint npcs)
    : base_partial( this )
    , log( &Cx::OFile::null() )
    , csp_base_pfmla(true)
    , urandom(pcidx, npcs)
    , optimal_nlayers_sum(0)
    , done_ck_fn(0)
    , done_ck_mem(0)
  {}
  bool init(const AddConvergenceOpt& opt);
  bool add(const Xn::Sys& sys, const StabilizationOpt& opt);
  bool done_ck() const {
    if (!done_ck_fn)  return false;
    return (0 != done_ck_fn (done_ck_mem));
  }
};


bool
coexist_ck(const Xn::ActSymm& a, const Xn::ActSymm& b);
void
RankDeadlocksMRV(vector<DeadlockConstraint>& dlsets,
                 const Xn::Net& topo,
                 const vector<uint>& actions,
                 const Cx::PFmla& deadlockPF);
bool
PickActionMRV(uint& ret_actId,
              const PartialSynthesis& tape,
              const AddConvergenceOpt& opt);

#endif

