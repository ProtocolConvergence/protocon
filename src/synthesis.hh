
#ifndef PartialSynthesis_HH_
#define PartialSynthesis_HH_
#include <fildesh/ostream.hh>

#include "cx/set.hh"
#include "cx/urandom.hh"
#include "pfmla.hh"
#include "inst.hh"
#include "promela.hh"
#include "xnsys.hh"
#include "prot-xfile.hh"
#include "conflictfamily.hh"
#include "stabilization.hh"

#include "namespace.hh"

class SynthesisCtx;
class PartialSynthesis;

static const bool DBog_RankDeadlocksMRV = false;

class DeadlockConstraint {
public:
  P::Fmla deadlockPF;
  Set<uint> candidates;
public:
  DeadlockConstraint() :
    deadlockPF(false)
  {}

  explicit DeadlockConstraint(const P::Fmla& _deadlockPF) :
    deadlockPF(_deadlockPF)
  {}
};

class AddConvergenceOpt {
public:
  enum PickActionHeuristic {
    MRVLitePick,
    LexPick,
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
  /* fildesh::ofstream log; */
  bool verify_found;

  bool randomize_pick;
  uint randomize_depth;
  bool system_urandom;
  bool force_disabling;
  bool pure_actions;
  bool prep_conflicts;
  bool fast_deadlock_mrv;
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
  Table< vector<uint> > solution_guesses;
  Set< uint > subset_solution_guesses;
  std::string livelock_ofilepath;
  uint n_livelock_ofiles;

  AddConvergenceOpt() :
    pick_method( MRVLitePick )
    , search_method( BacktrackSearch )
    , nicePolicy( NilNice )
    , pick_back_reach( false )
    /* , log("/dev/stderr") */
    , verify_found( true )
    , randomize_pick( true )
    , randomize_depth( 0 )
    , system_urandom( false )
    , force_disabling( false )
    , pure_actions( false )
    , prep_conflicts( false )
    , fast_deadlock_mrv( false )
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

  std::ostream* log;
  uint bt_level;
  uint failed_bt_level;
  bool directly_add_conflicts;
  bool no_conflict;
  bool no_partial;

  vector<uint> actions; ///< Chosen actions.
  Table<uint> picks; ///< Chosen actions, no inferred ones.
  vector<uint> candidates; ///< Candidate actions.
  P::Fmla deadlockPF; ///< Current deadlocks.
  X::Fmla lo_xn; ///< Under-approximation of the transition function.
  X::Fmla hi_xn; ///< Over-approximation of the transition function.
  X::Fmlae lo_xfmlae; ///< Under-approximation of the transition function.
  X::Fmlae hi_xfmlae; ///< Over-approximation of the transition function.
  P::Fmla hi_invariant;
  uint lo_nlayers;

  P::Fmla csp_pfmla;

  Table<PartialSynthesis> instances;  // Other instances of the parameterized system.

private:
  void initialize_log_as_dev_null();

public:
  explicit PartialSynthesis(SynthesisCtx* _ctx, uint idx=0)
    : ctx( _ctx )
    , sys_idx( idx )
    , log(NULL)
    , bt_level( 0 )
    , failed_bt_level( 0 )
    , directly_add_conflicts( false )
    , no_conflict( false )
    , no_partial( false )
    , lo_xn( false )
    , hi_xn( false )
    , hi_invariant( false )
    , lo_nlayers( 1 )
  {
    this->initialize_log_as_dev_null();
  }

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
      if (!(*this)[i].candidates.empty())
        return true;
    }
    return false;
  }

  bool candidate_ck(uint actidx) const {
    for (uint i = 0; i < this->sz(); ++i) {
      const vector<uint>& v = (*this)[i].candidates;
      for (uint j = 0; j < v.size(); ++j) {
        if (v[j] == actidx)
          return true;
      }
    }
    return false;
  }
  bool delegate_ck(uint actidx) const {
    for (uint i = 0; i < this->actions.size(); ++i) {
      if (this->actions[i] == actidx)
        return true;
    }
    return false;
  }

  bool deadlocks_ck() const {
    for (uint i = 0; i < this->sz(); ++i) {
      if ((*this)[i].deadlockPF.sat_ck())
        return true;
    }
    return false;
  }

  uint add_small_conflict_set(const Table<uint>& delpicks);
  bool check_forward(Set<uint>& adds, Set<uint>& dels, Set<uint>& rejs);
private:
  void useless_picks(Map<uint,uint>& changes, Set<uint>& allowed) const;
public:
  bool revise_actions_alone(Set<uint>& adds, Set<uint>& dels, Set<uint>& rejs, uint* ret_nlayers = 0);
  bool revise_actions(const Set<uint>& adds, const Set<uint>& dels, uint* ret_nlayers = 0);
  bool pick_action(uint act_idx);
  bool pick_actions(const vector<uint>& act_idcs);
  bool pick_actions_separately(const vector<uint>& act_idcs,
                               bool add_missing=true);
};

class SynthesisCtx {
public:
  PartialSynthesis base_partial;
  Table<const Xn::Sys*> systems;
  mutable fildesh::ofstream log;
  mutable fildesh::ofstream dev_null_ostream;
  PFmlaCtx csp_pfmla_ctx;
  P::Fmla csp_base_pfmla;
  URandom urandom;
  AddConvergenceOpt opt;
  Table<StabilizationOpt> stabilization_opts;
  uint optimal_nlayers_sum;
  Bool (*done_ck_fn) (void*);
  void* done_ck_mem;
  ConflictFamily conflicts;

  SynthesisCtx()
    : base_partial( this )
    , log("/dev/null")
    , dev_null_ostream("/dev/null")
    , csp_base_pfmla(true)
    , optimal_nlayers_sum(0)
    , done_ck_fn(0)
    , done_ck_mem(0)
  {}
  SynthesisCtx(uint pcidx, uint npcs)
    : base_partial( this )
    , log("/dev/null")
    , dev_null_ostream("/dev/null")
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
coexist_ck(const Xn::ActSymm& a, const Xn::ActSymm& b,
           const Xn::Net& topo,
           bool force_disabling=false, bool pure_actions=false);
void
RankDeadlocksMRV(vector<DeadlockConstraint>& dlsets,
                 const Xn::Net& topo,
                 const vector<uint>& actions,
                 const P::Fmla& deadlockPF);
bool
PickActionMRV(uint& ret_actId,
              const PartialSynthesis& partial,
              const AddConvergenceOpt& opt);

END_NAMESPACE
#endif

