
#include "ordersyn.hh"
#include "xnsys.hh"
#include <algorithm>

#include "cx/urandom.h"
#include "cx/fileb.hh"
#include "protoconfile.hh"
#include "stability.hh"
#include <signal.h>

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
  //tape.directly_add_conflicts = true;

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
  if (cycle_ck(tape.loXnRel, ~invariant)) {
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

  void
oput_conflicts (const ConflictFamily& conflicts, const Cx::String& ofilename)
{
  Cx::OFileB conflicts_of;
  conflicts_of.open(ofilename.cstr());
  conflicts_of << conflicts;
}

  void
oput_conflicts (const ConflictFamily& conflicts, Cx::String ofilename, uint pcidx)
{
  ofilename += pcidx;
  oput_conflicts(conflicts, ofilename);
}

static volatile bool* done_flag = false;

  void
set_done_flag (int sig)
{
  (void) sig;
  if (done_flag)
    *done_flag = true;
}

  bool
flat_backtrack_synthesis(vector<uint>& ret_actions,
                         const ProtoconFileOpt& infile_opt,
                         const ProtoconOpt& exec_opt,
                         const AddConvergenceOpt& global_opt)
{
  bool done = false;
  bool solution_found = false;
  uint NPcs = 0;
  ConflictFamily conflicts;

  done_flag = &done;
  signal(SIGINT, set_done_flag);
  signal(SIGTERM, set_done_flag);

  if (global_opt.conflicts_xfilename)
  {
    Cx::XFileB conflicts_xf;
    conflicts_xf.open(global_opt.conflicts_xfilename);
    conflicts_xf >> conflicts;
    if (!conflicts_xf.good()) {
      DBog1( "Bad read from conflicts file: %s", global_opt.conflicts_xfilename );
      return false;
    }
    conflicts.trim(global_opt.max_conflict_sz);
    conflicts.oput_conflict_sizes(DBogOF);
  }

  Cx::Table< FlatSet<uint> > flat_conflicts;
  if (exec_opt.task == ProtoconOpt::MinimizeConflictsTask) {
    conflicts.all_conflicts(flat_conflicts);
  }

#pragma omp parallel shared(done,NPcs,solution_found,ret_actions,conflicts,flat_conflicts)
  {
  Sign good = 1;
  AddConvergenceOpt opt(global_opt);
  uint PcIdx;
  ConflictFamily working_conflicts = conflicts;
  Cx::OFileB log_ofile;
#pragma omp critical
  {
    PcIdx = NPcs;
    ++ NPcs;
  }

#pragma omp barrier
  opt.sys_pcidx = PcIdx;
  opt.sys_npcs = NPcs;
  opt.random_one_shot = true;
  if (exec_opt.log_ofilename) {
    Cx::String ofilename( exec_opt.log_ofilename );
    ofilename += PcIdx;
    log_ofile.open(ofilename);
    opt.log = &log_ofile;
  }
  else if (NPcs > 1) {
    opt.log = &Cx::OFile::null();
  }
  //opt.log = &DBogOF;
  opt.verify_found = false;

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
#pragma omp flush (done)
  }

#pragma omp critical (DBog)
  DBog1( "BEGIN! %u", PcIdx );

  synctx.conflicts = working_conflicts;
  working_conflicts.clear();
  {
    Set<uint> impossible( synctx.conflicts.impossible_set );
    impossible &= Set<uint>(synlvl.candidates);
    if (!impossible.empty())
      synlvl.revise_actions(sys, Set<uint>(), impossible);
  }

  if (exec_opt.task == ProtoconOpt::MinimizeConflictsTask)
  {
#pragma omp for schedule(dynamic)
    for (uint conflict_idx = 0; conflict_idx < flat_conflicts.sz(); ++conflict_idx) {
      uint old_sz = flat_conflicts[conflict_idx].sz();
      if (!done && old_sz > 1) {
        *opt.log
          << "pcidx:" << PcIdx
          << " conflict:" << conflict_idx << "/" << flat_conflicts.sz()
          << " sz:" << old_sz;
        opt.log->flush();

        uint new_sz =
          synlvl.add_small_conflict_set(sys, flat_conflicts[conflict_idx]);

        *opt.log
          << "DONE: pcidx:" << PcIdx
          << " conflict:" << conflict_idx << "/" << flat_conflicts.sz()
          << " old_sz:" << old_sz << " new_sz:" << new_sz;
        opt.log->flush();
      }
    }

#pragma omp critical (DBog)
    conflicts.add_conflicts(synctx.conflicts);

    conflicts.oput_conflict_sizes(*opt.log);
  }

  vector<uint> actions;
  if (exec_opt.task == ProtoconOpt::SearchTask)
  for (uint trial_idx = 0; !done && (opt.ntrials == 0 || trial_idx < opt.ntrials); ++trial_idx)
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

#pragma omp critical (DBog)
    {
    if (done)
    {}
    else if (found)
    {
      if (!global_opt.try_all)
        done = true;
      solution_found = true;
      ret_actions = actions;
      *opt.log << "SOLUTION FOUND!";

    }
    if (!done || global_opt.conflicts_ofilename)
    {
      synctx.conflicts.add_conflicts(conflicts);
      synctx.conflicts.trim(global_opt.max_conflict_sz);

      conflicts = synctx.conflicts;

      if (opt.search_method == opt.RankShuffleSearch)
        DBogOF << "pcidx:" << PcIdx << " trial:" << trial_idx+1 << " actions:" << actions.size() << '\n';
      else
        DBogOF << "pcidx:" << PcIdx << " trial:" << trial_idx+1 << " depth:" << synlvl.failed_bt_level << '\n';
      DBogOF.flush();
    }
    }

    synctx.conflicts.oput_conflict_sizes(*opt.log);
    if (opt.search_method == opt.RankShuffleSearch)
      *opt.log << "pcidx:" << PcIdx << " trial:" << trial_idx+1 << " actions:" << actions.size() << '\n';
    else
      *opt.log << "pcidx:" << PcIdx << " trial:" << trial_idx+1 << " depth:" << synlvl.failed_bt_level << '\n';
    opt.log->flush();

    if (global_opt.snapshot_conflicts && global_opt.conflicts_ofilename)
      oput_conflicts (synctx.conflicts, global_opt.conflicts_ofilename, PcIdx);

    if (!done) {
      Set<uint> impossible( synctx.conflicts.impossible_set );
      impossible &= Set<uint>(synlvl.candidates);
      if (!impossible.empty())
        synlvl.revise_actions(sys, Set<uint>(), impossible);
    }

    //check_conflict_sets(conflict_sets);
  }
  }

  conflicts.trim(global_opt.max_conflict_sz);
  if (global_opt.conflicts_ofilename)
    oput_conflicts (conflicts, global_opt.conflicts_ofilename);

  if (global_opt.snapshot_conflicts && global_opt.conflicts_ofilename)
  {
    for (uint i = 0; i < NPcs; ++i) {
      Cx::String ofilename( global_opt.conflicts_ofilename );
      ofilename += i;
      remove(ofilename.cstr());
    }
  }

  return solution_found;
}

