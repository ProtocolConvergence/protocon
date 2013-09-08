
#include "ordersyn.hh"
#include "xnsys.hh"
#include <algorithm>

#include "cx/urandom.h"
#include "cx/fileb.hh"
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
check_conflict_sets(const Cx::LgTable< Set<uint> >& conflict_sets)
{
  for (ujint i = conflict_sets.begidx();
       i != Max_ujint;
       i = conflict_sets.nextidx(i))
  {
    const Set<uint>& a = conflict_sets[i];
    for (ujint j = conflict_sets.nextidx(i);
         j != Max_ujint;
         j = conflict_sets.nextidx(j))
    {
      const Set<uint>& b = conflict_sets[j];
      Claim( !a.subseteq_ck(b) );
      Claim( !b.subseteq_ck(a) );
    }
  }
}

static
  bool
try_order_synthesis(vector<uint>& ret_actions,
                    const Xn::Sys& sys,
                    StabilitySynLvl& tape)
{
  ret_actions.clear();

  while (tape.candidates.size() > 0)
  {
    uint actidx = tape.candidates[0];
    StabilitySynLvl next( tape );
    if (next.pick_action(sys, actidx))
    {
      tape = next;
    }
    else
    {
      if (tape.ctx->done && *tape.ctx->done)
        return false;

      if (!tape.revise_actions(sys, Set<uint>(), Set<uint>(actidx)))
      {
        ret_actions = tape.actions;
        return false;
      }
    }
    if (tape.ctx->done && *tape.ctx->done)
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
flat_backtrack_synthesis(vector<uint>& ret_actions,
                         const ProtoconFileOpt& infile_opt,
                         const AddConvergenceOpt& global_opt)
{
  const uint ntrials = 300;

  bool done = false;
  bool solution_found = false;
  uint NPcs = 0; 
  ConflictFamily conflicts;

  if (false)
  {
    Cx::XFileB conflicts_xf;
    conflicts_xf.open("saved_working_conflicts");
    conflicts_xf >> conflicts;
    conflicts.oput_conflict_sizes(DBogOF);
  }

#ifdef _OPENMP
#pragma omp parallel shared(done,NPcs,solution_found,ret_actions,conflicts)
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
  //opt.bt_dbog = true;

  Xn::Sys sys;
  DoLegit(good, "reading file")
    good =
    ReadProtoconFile(sys, infile_opt);

  StabilitySyn synctx( PcIdx, NPcs );
  StabilitySynLvl synlvl( &synctx );

  DoLegit(good, "initialization")
    good =
    InitStabilitySyn(synctx, synlvl, sys, opt);

  synctx.done = &done;

  Cx::Table< Cx::Table<uint> > act_layers;
  if (opt.search_method == opt.RankShuffleSearch)
  {
    DoLegit(good, "ranking actions")
      good =
      rank_actions (act_layers, sys.topology,
                    synlvl.candidates,
                    synlvl.hiXnRel,
                    synlvl.hi_invariant);
  }

  if (!good)
  {
    done = true;
#ifdef _OPENMP
#pragma omp flush (done)
#endif
  }

#ifdef _OPENMP
#pragma omp critical (DBog)
#endif
  DBog1( "BEGIN! %u", PcIdx );

  ConflictFamily working_conflicts;
  {
    synctx.conflicts = conflicts;

    Set<uint> impossible( synctx.conflicts.impossible_set );
    impossible &= Set<uint>(synlvl.candidates);
    if (!impossible.empty())
      synlvl.revise_actions(sys, Set<uint>(), impossible);
  }

  vector<uint> actions;
  for (uint trial_idx = 0; !done && trial_idx < ntrials; ++trial_idx)
  {
    bool found = false;
    if (opt.search_method == opt.RankShuffleSearch)
    {
      StabilitySynLvl tape( synlvl );
      vector<uint>& candidates = tape.candidates;
      candidates.clear();
      for (uint i = 0; i < act_layers.sz(); ++i) {
        uint off = candidates.size();
        for (uint j = 0; j < act_layers[i].sz(); ++j) {
          candidates.push_back(act_layers[i][j]);
        }
        synctx.urandom.shuffle(&candidates[off], act_layers[i].sz());
      }
      found = try_order_synthesis(actions, sys, tape);
    }
    else
    {
      found = AddConvergence(actions, sys, synlvl, opt);
    }

#ifdef _OPENMP
#pragma omp critical (DBog)
#endif
    {
    if (done)
    {}
    else if (found)
    {
      done = true;
      solution_found = true;
      ret_actions = actions;
      DBog0("SOLUTION FOUND!");

    }
    else
    {
      synctx.conflicts.add_conflicts(conflicts);

      conflicts = synctx.conflicts;
      conflicts.oput_conflict_sizes(DBogOF);

      if (opt.search_method == opt.RankShuffleSearch)
        DBog3("pcidx:%u trial:%u actions:%u", PcIdx, trial_idx+1, actions.size());
      else
        DBog3("pcidx:%u trial:%u depth:%u", PcIdx, trial_idx+1, synlvl.failed_bt_level);
    }
    }

    if (!done) {
      Set<uint> impossible( synctx.conflicts.impossible_set );
      impossible &= Set<uint>(synlvl.candidates);
      if (!impossible.empty())
        synlvl.revise_actions(sys, Set<uint>(), impossible);
    }

    //check_conflict_sets(conflict_sets);
  }
  }

  return solution_found;
}

