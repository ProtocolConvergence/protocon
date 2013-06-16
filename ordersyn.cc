
#include "ordersyn.hh"
#include "xnsys.hh"
#include <algorithm>

#include "cx/gmrand.h"
#include "protoconfile.hh"

static std::ostream& DBogOF = std::cerr;

  bool
candidate_actions(vector<uint>& candidates, const Xn::Sys& sys)
{
  const Xn::Net& topo = sys.topology;

  if (sys.liveLegit && !sys.synLegit) {
    DBog0( "For liveness in the invariant, we must be able to add actions there!" );
    return false;
  }

  if (sys.invariant.tautology_ck(false)) {
    DBog0( "Invariant is empty!" );
    return false;
  }

  if (sys.invariant.tautology_ck(true)) {
    DBog0( "All states are invariant!" );
    if (!sys.shadowVblCk()) {
      return true;
    }
  }

  for (uint i = 0; i < topo.n_possible_acts; ++i) {
    bool add = true;

    Xn::ActSymm act;
    topo.action(act, i);
    const PF& actPF = topo.action_pfmla(i);

    // Check for self-loops.
    if (add) {
      const Xn::PcSymm& pc = *act.pc_symm;
      bool selfloop = true;
      for (uint j = 0; j < pc.wvbl_symms.sz(); ++j) {
        if (act.assign(j) != act.aguard(j)) {
          selfloop = false;
        }
      }
      add = !selfloop;
      if (false && selfloop) {
        OPut((DBogOF << "Action " << i << " is a self-loop: "), act) << '\n';
      }
    }

    if (add && !sys.shadowVblCk() && sys.invariant.overlap_ck(actPF)) {
      // This action does starts in the invariant.
      // If /!sys.synLegit/, we shouldn't add any actions
      // within the legitimate states, even if closure isn't broken.
      if (!sys.synLegit || (~sys.invariant).overlap_ck(actPF.img(sys.invariant))) {
        add = false;
        if (false) {
          OPut((DBogOF << "Action " << i << " breaks closure: "), act) << '\n';
        }
      }
    }

    if (add) {
      candidates.push_back(i);
    }
  }
  return true;
}

/**
 * Check if two actions can coexist in a
 * deterministic protocol of self-disabling processes.
 */
  bool
coexist_ck(const Xn::ActSymm& a, const Xn::ActSymm& b)
{
  if (a.pc_symm != b.pc_symm)  return true;
  const Xn::PcSymm& pc = *a.pc_symm;

  bool enabling = true;
  bool deterministic = false;
  for (uint j = 0; enabling && j < pc.rvbl_symms.sz(); ++j) {
    if (a.guard(j) != b.guard(j)) {
      deterministic = true;
      if (!pc.write_ck(j)) {
        enabling = false;
      }
    }
  }

  if (!deterministic)  return false;
  if (!enabling)  return true;

  bool a_enables = true;
  bool b_enables = true;
  for (uint j = 0; j < pc.wvbl_symms.sz(); ++j) {
    if (a.assign(j) != b.aguard(j)) {
      a_enables = false;
    }
    if (b.assign(j) != a.aguard(j)) {
      b_enables = false;
    }
  }
  return !(a_enables || b_enables);
}

static
  bool
try_order_synthesis(vector<uint>& actions, const Xn::Sys& sys,
                    const vector<uint>& candidates)
{
  const Xn::Net& topo = sys.topology;
  actions.clear();

  Cx::PFmla xn_pfmla( false );
  Cx::PFmla deadlock_pfmla( !sys.invariant );

  Xn::ActSymm act;
  Xn::ActSymm act_tmp;
  for (uint i = 0; i < candidates.size(); ++i)
  {
    bool add = true;
    const uint act_idx = candidates[i];
    topo.action(act, act_idx);
    for (uint j = 0; add && j < actions.size(); ++j)
    {
      topo.action(act_tmp, actions[j]);
      add = add && coexist_ck(act, act_tmp);
    }
    if (!add)  continue;
    const Cx::PFmla& act_pf = topo.action_pfmla(act_idx);
    Cx::PFmla pre_pf( act_pf.pre() );
    if (!pre_pf.overlap_ck(deadlock_pfmla))
      continue;
    if (CycleCk(xn_pfmla | act_pf, Cx::PFmla(true)))
      continue;

    actions.push_back(act_idx);
    xn_pfmla |= act_pf;
    deadlock_pfmla -= pre_pf;

    if (deadlock_pfmla.tautology_ck(false)) {
      return true;
    }
  }
  return false;
}

class RNG {
public:
  GMRand gmrand;

  RNG() {
    init_GMRand( &gmrand );
  }
  explicit RNG(uint i) {
    init1_GMRand( &gmrand, i );
  }
  int operator()(int n) {
    return (int) uint_GMRand (&gmrand, (uint) n);
  }
};

  bool
ordering_synthesis(vector<uint>& ret_actions, const char* infile_path)
{
  const uint ntrials = 300;

  bool done = false;
  bool solution_found = false;
  uint NPcs = 0; 
#ifdef _OPENMP
#pragma omp parallel shared(done,NPcs,solution_found)
#endif
  {
  uint PcIdx;
#ifdef _OPENMP
#pragma omp critical
#endif
  {
    PcIdx = NPcs;
    ++ NPcs;
  }

  Xn::Sys sys;
  ReadProtoconFile(sys, infile_path);

  vector<uint> candidates;
  bool good = candidate_actions(candidates, sys);

#ifdef _OPENMP
#pragma omp critical
#endif
  {
    if (good && candidates.size() == 0) {
      solution_found = true;
    }
    if (!good)
      done = true;
  }

  RNG rng( PcIdx );
  std::vector<uint> tmp_candidates;
  uint i = 0;

  vector<uint> actions;
  while (!done && i < ntrials)
  {
    tmp_candidates = candidates;
    std::random_shuffle(tmp_candidates.begin(), tmp_candidates.end(), rng);
#ifdef _OPENMP
#pragma omp critical
#endif
    {
      DBog2( "trial %u %u", PcIdx, i+1 );
#if 0
      DBogOF << "[";
      for (uint j = 0; j < tmp_candidates.size(); ++j) {
        if (j > 0)  DBogOF << ", ";
        DBogOF << tmp_candidates[j];
      }
      DBogOF << "]\n";
#endif
    }

    bool found =
      try_order_synthesis(actions, sys, tmp_candidates);

#ifdef _OPENMP
#pragma omp critical
#endif
    {
      if (found) {
        done = true;
        ret_actions = actions;
        solution_found = true;
      }
    }
    ++ i;
  }
  }

  return solution_found;
}

