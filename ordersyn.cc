
#include "ordersyn.hh"
#include "xnsys.hh"
#include <algorithm>

#include "cx/urandom.h"
#include "protoconfile.hh"
#include "stability.hh"

bool
AddConvergence(vector<uint>& retActions,
               const Xn::Sys& sys,
               StabilitySynLvl& tape,
               const AddConvergenceOpt& opt);
bool
InitStabilitySyn(StabilitySyn& synctx,
                 StabilitySynLvl& tape,
                 const Xn::Sys& sys,
                 const AddConvergenceOpt& opt);

  void
rank_states (Cx::Table<Cx::PFmla>& state_layers,
             const Cx::PFmla& xn_pf, const Cx::PFmla& legit)
{
  state_layers.resize(0);
  state_layers.push(legit);

  PF visit_pf( legit );
  PF layer_pf( xn_pf.pre(legit) - visit_pf );
  while (!layer_pf.tautology_ck(false)) {
    state_layers.push(layer_pf);
    visit_pf |= layer_pf;
    layer_pf = xn_pf.pre(layer_pf) - visit_pf;
  }
  if (!visit_pf.tautology_ck(true)) {
  }
}

//  void
//rank_actions (Cx::Table<Cx::PFmla>& act_layers,
//              const Cx::PFmla& xn_pf, const Cx::PFmla& legit)
//{
//}

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
#if 0
  vector<uint> skipped_candidates = candidates;
  while (skipped_candidates.size() > 0)
  {
    vector<uint> candidates;
    candidates = skipped_candidates;
    skipped_candidates.clear();
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

      if (act_pf.img() <= deadlock_pfmla)
      {
        skipped_candidates.push_back(act_idx);
        continue;
      }

      actions.push_back(act_idx);
      xn_pfmla |= act_pf;
      deadlock_pfmla -= pre_pf;

      if (deadlock_pfmla.tautology_ck(false)) {
        return true;
      }
    }
    if (skipped_candidates.size() == candidates.size()) {
      // No candidates reach the current state.
      break;
    }
  }
  DBog1( "actions.size() = %u", (uint) actions.size() );
#else
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
#endif
  return false;
}

  bool
flat_backtrack_synthesis(vector<uint>& ret_actions, const char* infile_path,
                         const AddConvergenceOpt& global_opt)
{
  const uint ntrials = 300;

  bool done = false;
  bool solution_found = false;
  uint NPcs = 0; 
#ifdef _OPENMP
#pragma omp parallel shared(done,NPcs,solution_found)
#endif
  {
  AddConvergenceOpt opt(global_opt);
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

#ifdef _OPENMP
#pragma omp barrier
#endif
  opt.sys_pcidx = PcIdx;
  opt.sys_npcs = NPcs;
  opt.random_one_shot = true;
  opt.bt_dbog = false;

  StabilitySyn synctx( PcIdx, NPcs );
  StabilitySynLvl synlvl( &synctx );
  InitStabilitySyn(synctx, synlvl, sys, opt);
  synctx.solution_found = &solution_found;

  for (uint i = 0; !done && i < ntrials; ++i)
  {
#ifdef _OPENMP
#pragma omp critical
#endif
    DBog2( "trial %u %u", PcIdx, i+1 );


    vector<uint> actions;
    bool found =
      AddConvergence(actions, sys, synlvl, opt);

    if (found)
    {
#ifdef _OPENMP
#pragma omp critical
#endif
      {
      done = true;
      ret_actions = actions;
      solution_found = true;
      DBog0("SOLUTION FOUND!");
      }
    }
  }
  }

  return solution_found;
}


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

#ifdef _OPENMP
#pragma omp barrier
#endif

  URandom shufseq[1];
  init2_URandom (shufseq, PcIdx, NPcs);
  std::vector<uint> tmp_candidates;

  vector<uint> actions;
  for (uint i = 0; !done && i < ntrials; ++i)
  {
    tmp_candidates = candidates;
    shuffle_uints_URandom (shufseq, &tmp_candidates[0], tmp_candidates.size());
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

    if (found)
    {
#ifdef _OPENMP
#pragma omp critical
#endif
      {
        done = true;
        ret_actions = actions;
        solution_found = true;
      }
    }
  }
  }

  return solution_found;
}

