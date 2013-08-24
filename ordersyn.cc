
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


  bool
flat_backtrack_synthesis(vector<uint>& ret_actions,
                         const ProtoconFileOpt& infile_opt,
                         const AddConvergenceOpt& global_opt)
{
  const uint ntrials = 300;

  bool done = false;
  bool solution_found = false;
  uint NPcs = 0; 
  Cx::LgTable< Set<uint> > conflict_sets;

#ifdef _OPENMP
#pragma omp parallel shared(done,NPcs,solution_found,conflict_sets)
#endif
  {
  Sign good = 1;
  AddConvergenceOpt opt(global_opt);
  uint PcIdx;
#ifdef _OPENMP
#pragma omp critical
#endif
  {
    PcIdx = NPcs;
    ++ NPcs;
  }

#ifdef _OPENMP
#pragma omp barrier
#endif
  opt.sys_pcidx = PcIdx;
  opt.sys_npcs = NPcs;
  opt.random_one_shot = true;
  opt.bt_dbog = false;

  Xn::Sys sys;
  DoLegit(good, "reading file")
    good =
    ReadProtoconFile(sys, infile_opt);

  StabilitySyn synctx( PcIdx, NPcs );
  StabilitySynLvl synlvl( &synctx );

  DoLegit(good, "initialization")
    good =
    InitStabilitySyn(synctx, synlvl, sys, opt);

  synctx.solution_found = &solution_found;

  if (!good)
  {
    done = true;
#ifdef _OPENMP
#pragma omp flush (done)
#endif
  }

  for (uint trialidx = 0; !done && trialidx < ntrials; ++trialidx)
  {
#ifdef _OPENMP
#pragma omp critical (DBog)
#endif
    DBog2( "trial %u %u", PcIdx, trialidx+1 );

    vector<uint> actions;
    bool found =
      AddConvergence(actions, sys, synlvl, opt);

#ifdef _OPENMP
#pragma omp critical (DBog)
#endif
    {
    if (found)
    {
      done = true;
      solution_found = true;
      ret_actions = actions;
      DBog0("SOLUTION FOUND!");
    }
    else
    {
      for (ujint i = conflict_sets.begidx(); i != Max_ujint; i = conflict_sets.nextidx(i))
        synctx.add_conflict_set(conflict_sets[i]);

      conflict_sets = synctx.conflict_sets;
    }
    }
  }
  }

  return solution_found;
}

static
  bool
try_order_synthesis(vector<uint>& ret_actions,
                    const Xn::Sys& sys,
                    StabilitySynLvl tape)
{
  ret_actions.clear();

  while (tape.candidates.size() > 0)
  {
    uint actidx = tape.candidates[0];
    StabilitySynLvl next( tape );
    if (next.revise_actions(sys, Set<uint>(actidx), Set<uint>()))
    {
      tape = next;
    }
    else
    {
      if (*tape.ctx->solution_found)
        return false;

      if (!tape.revise_actions(sys, Set<uint>(), Set<uint>(actidx)))
      {
        ret_actions = tape.actions;
        return false;
      }
    }
    if (*tape.ctx->solution_found)
      return false;
  }

  Claim( !tape.deadlockPF.sat_ck() );
  const Cx::PFmla& invariant = tape.hi_invariant;
  if (CycleCk(tape.loXnRel, ~invariant)) {
    DBog0( "Why are there cycles?" );
    return false;
  }
  if (!WeakConvergenceCk(sys, tape.loXnRel, invariant)) {
    if (!invariant.tautology_ck(false)) {
      DBog0( "Why does weak convergence not hold?" );
    }
    return false;
  }
  ret_actions = tape.actions;
  return true;
}

static
  bool
rank_states (Cx::Table<Cx::PFmla>& state_layers,
             const Cx::PFmla& xn, const Cx::PFmla& legit)
{
  state_layers.resize(0);
  state_layers.push(legit);

  PF visit_pf( legit );
  PF layer_pf( xn.pre(legit) - visit_pf );
  while (!layer_pf.tautology_ck(false)) {
    state_layers.push(layer_pf);
    visit_pf |= layer_pf;
    layer_pf = xn.pre(layer_pf) - visit_pf;
  }
  return (visit_pf.tautology_ck(true));
}

static
  bool
rank_actions (Cx::Table< Cx::Table<uint> >& act_layers,
              const Xn::Net& topo,
              const vector<uint>& candidates,
              const Cx::PFmla& xn,
              const Cx::PFmla& legit)
{
  Cx::Table<Cx::PFmla> state_layers;
  if (!rank_states (state_layers, xn, legit))
    return false;

  act_layers.resize(state_layers.sz()+1);
  for (uint i = 0; i < candidates.size(); ++i) {
    const uint actidx = candidates[i];
    const Cx::PFmla& act_pf = topo.action_pfmla(actidx);
    bool found = false;
    for (uint j = 1; !found && j < state_layers.sz(); ++j) {
      if (act_pf.img(state_layers[j]).overlap_ck(state_layers[j-1])) {
        act_layers[j].push(actidx);
        found = true;
      }
    }
    if (!found) {
      act_layers.top().push(actidx);
    }
  }
  return true;
}

  bool
ordering_synthesis(vector<uint>& ret_actions,
                   const ProtoconFileOpt& infile_opt)
{
  const uint ntrials = 300;

  bool done = false;
  bool solution_found = false;
  uint NPcs = 0; 
  Cx::LgTable< Set<uint> > conflict_sets;

#ifdef _OPENMP
#pragma omp parallel shared(done,NPcs,solution_found,conflict_sets)
#endif
  {
  Sign good = 1;
  AddConvergenceOpt opt;
  uint PcIdx;
#ifdef _OPENMP
#pragma omp critical
#endif
  {
    PcIdx = NPcs;
    ++ NPcs;
  }

#ifdef _OPENMP
#pragma omp barrier
#endif
  opt.sys_pcidx = PcIdx;
  opt.sys_npcs = NPcs;
  opt.bt_dbog = false;

  Xn::Sys sys;
  DoLegit(good, "reading file")
    good =
    ReadProtoconFile(sys, infile_opt);

  StabilitySyn synctx( PcIdx, NPcs );
  StabilitySynLvl synlvl( &synctx );

  DoLegit(good, "initialization")
    good =
    InitStabilitySyn(synctx, synlvl, sys, opt);

  synctx.solution_found = &solution_found;

  Cx::Table< Cx::Table<uint> > act_layers;
  DoLegit(good, "ranking actions")
    good =
    rank_actions (act_layers, sys.topology,
                  synlvl.candidates,
                  synlvl.hiXnRel,
                  synlvl.hi_invariant);

  if (!good)
  {
      done = true;
#ifdef _OPENMP
#pragma omp flush (done)
#endif
  }

  vector<uint> actions;
  for (uint trial_idx = 0; !done && trial_idx < ntrials; ++trial_idx)
  {
    vector<uint>& candidates = synlvl.candidates;
    candidates.clear();
    for (uint i = 0; i < act_layers.sz(); ++i) {
      uint off = candidates.size();
      for (uint j = 0; j < act_layers[i].sz(); ++j) {
        candidates.push_back(act_layers[i][j]);
      }
      synctx.urandom.shuffle(&candidates[off], act_layers[i].sz());
    }

#ifdef _OPENMP
#pragma omp critical (DBog)
#endif
    DBog2( "trial %u %u", PcIdx, trial_idx+1 );

    bool found =
      try_order_synthesis(actions, sys, synlvl);

#ifdef _OPENMP
#pragma omp critical (DBog)
#endif
    {
    if (!solution_found)
      DBog2("pcidx:%u depth:%u", PcIdx, actions.size());

    if (found && !solution_found)
    {
      solution_found = true;
      done = true;
      ret_actions = actions;
      DBog0("SOLUTION FOUND!");
    }
    else
    {
      for (ujint i = conflict_sets.begidx(); i != Max_ujint; i = conflict_sets.nextidx(i))
        synctx.add_conflict_set(conflict_sets[i]);

      conflict_sets = synctx.conflict_sets;
    }
    }
  }
  }

  return solution_found;
}

