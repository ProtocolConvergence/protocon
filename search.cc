
#include "search.hh"
#include "xnsys.hh"
#include <algorithm>

#include "cx/urandom.hh"
#include "cx/fileb.hh"
#include "opt.hh"
#include "pla.hh"
#include "protoconfile.hh"
#include "stabilization.hh"
#include "synthesis.hh"
#include <signal.h>
#include <errno.h>

#ifdef _OPENMP
#include <omp.h>
#endif

static bool
verify_solutions(const PartialSynthesis& inst, StabilizationCkInfo* info)
{
  for (uint i = 0; i < inst.sz(); ++i) {
    if (!inst[i].no_partial)
      continue;
    *inst.log << "Verifying solution for system " << i << "..." << inst.log->endl();
    if (!stabilization_ck(*inst[i].log, *inst[i].ctx->systems[i], inst[i].actions, info)) {
      if (i == inst.sz()-1 && info && info->livelock_exists && !!inst.ctx->opt.livelock_ofilepath) {
        Cx::OFileB ofb;
        ofb.open(inst.ctx->opt.livelock_ofilepath + "." + inst.ctx->opt.sys_pcidx + "." + inst.ctx->opt.n_livelock_ofiles++);
        oput_protocon_file(ofb, *inst.ctx->systems[i], false, inst[i].actions);
      }
      *inst[i].log << "Solution was NOT self-stabilizing." << inst[i].log->endl();
      return false;
    }
  }
  for (uint i = 0; i < inst.sz(); ++i) {
    if (inst[i].no_partial || !inst.ctx->opt.verify_found)
      continue;
    *inst.log << "Verifying solution for system " << i << "..." << inst.log->endl();
    if (!stabilization_ck(*inst[i].log, *inst[i].ctx->systems[i], inst[i].actions, info)) {
      *inst[i].log << "Solution was NOT self-stabilizing." << inst[i].log->endl();
      return false;
    }
  }
  return true;
}

/**
 * Add convergence to a system.
 * The system will therefore be self-stabilizing.
 * This is the recursive function.
 *
 * \return  True iff convergence could be added.
 */
  bool
AddConvergence(vector<uint>& ret_actions,
               PartialSynthesis& base_inst,
               const AddConvergenceOpt& opt)
{
  Cx::LgTable<PartialSynthesis> bt_stack;
  SynthesisCtx& synctx = *base_inst.ctx;

  base_inst.bt_level = 0;
  base_inst.failed_bt_level = 0;
  bt_stack.push(base_inst);
  uint stack_idx = 0;

  while (true) {
    PartialSynthesis& inst = bt_stack[stack_idx];
    if (synctx.done_ck()) {
      base_inst.failed_bt_level = inst.failed_bt_level;
      return false;
    }

    if (opt.max_depth > 0 && inst.bt_level >= opt.max_depth) {
      base_inst.failed_bt_level = opt.max_depth;
      return false;
    }

    if (!inst.candidates_ck()) {
      StabilizationCkInfo info;
      if (verify_solutions(inst, &info))  break;

      const bool early_return = !info.livelock_exists;
      if (info.livelock_exists) {
        if (!early_return) {
          *inst.log << "backtrack from lvl:" << inst.bt_level << inst.log->endl();
        }
        inst.ctx->conflicts.add_conflict(info.livelock_actions);
        inst.add_small_conflict_set(inst.picks);
      }
      stack_idx = decmod(stack_idx, 1, bt_stack.sz());
      if (bt_stack[stack_idx].bt_level >= inst.bt_level) {
        base_inst.failed_bt_level = bt_stack[stack_idx].bt_level;
        return false;
      }
      if (early_return)
        return false;
      else
        continue;
    }

    // Pick the action.
    uint actidx = 0;
    if (!PickActionMCV(actidx, inst, opt)) {
      DBog0("Cannot resolve all deadlocks!");
      inst.add_small_conflict_set(inst.picks);
      return false;
    }

    uint next_idx;
    if (opt.max_height == 0 || bt_stack.sz() < opt.max_height) {
      next_idx = stack_idx + 1;
      if (next_idx == bt_stack.sz())
        bt_stack.push(PartialSynthesis(&synctx));
    }
    else {
      next_idx = incmod(stack_idx, 1, bt_stack.sz());
    }
    PartialSynthesis& next = bt_stack[next_idx];
    next = inst;
    next.godeeper1();
    next.failed_bt_level = next.bt_level;

    if (next.pick_action(actidx))
    {
      stack_idx = next_idx;
      continue;
    }

    if (synctx.done_ck()) {
      base_inst.failed_bt_level = inst.failed_bt_level;
      return false;
    }

    while (!bt_stack[stack_idx].revise_actions(Set<uint>(), Set<uint>(actidx)))
    {
      PartialSynthesis& inst = bt_stack[stack_idx];
      *inst.log << "backtrack from lvl:" << inst.bt_level << inst.log->endl();
      inst.add_small_conflict_set(inst.picks);

      stack_idx = decmod(stack_idx, 1, bt_stack.sz());

      if (bt_stack[stack_idx].bt_level >= inst.bt_level) {
        base_inst.failed_bt_level = bt_stack[stack_idx].bt_level;
        return false;
      }

      if (synctx.done_ck()) {
        base_inst.failed_bt_level = inst.failed_bt_level;
        return false;
      }
      actidx = inst.picks.top();
    }
  }

  PartialSynthesis& inst = bt_stack[stack_idx];
  Claim(!inst.deadlockPF.sat_ck());
  ret_actions = inst.actions;
  return true;
}

/**
 * Add convergence to a system.
 * The system will therefore be self-stabilizing.
 *
 * \param sys  System definition. It is modified if convergence is added.
 * \return  True iff convergence could be added.
 */
  bool
AddConvergence(Xn::Sys& sys, const AddConvergenceOpt& opt)
{
  SynthesisCtx synctx;
  if (!synctx.init(sys, opt))
    return false;
  PartialSynthesis& inst = synctx.base_inst;

  vector<uint> ret_actions;
  bool found = AddConvergence(ret_actions, inst, opt);
  if (!found)  return false;

  sys.actions = ret_actions;
  return true;
}


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

  bool
try_order_synthesis(vector<uint>& ret_actions,
                    PartialSynthesis& inst)
{
  for (uint i = 0; i < inst.sz(); ++i) {
    //inst[i].noconflicts = true;
  }
  ret_actions.clear();
  //inst.directly_add_conflicts = true;

  while (inst.candidates_ck())
  {
      uint actidx;
    for (uint i = 0; i < inst.sz(); ++i) {
      if (inst[i].no_partial)  continue;
      actidx = inst[i].candidates[0];
    }
    PartialSynthesis next( inst );
    if (next.pick_action(actidx))
    {
      inst = next;
    }
    else
    {
      if (inst.ctx->done_ck())
        return false;

      if (!inst.revise_actions(Set<uint>(), Set<uint>(actidx)))
      {
        ret_actions = inst.actions;
        return false;
      }
    }
    if (inst.ctx->done_ck())
      return false;
  }

  Claim( !inst.deadlockPF.sat_ck() );
  StabilizationCkInfo info;
  if (!verify_solutions(inst, &info)) {
    if (info.livelock_exists) {
      inst.ctx->conflicts.add_conflict(info.livelock_actions);
    }
    inst.add_small_conflict_set(inst.picks);
    return false;
  }
  ret_actions = inst.actions;
  return true;
}


static
  bool
rank_states (Cx::Table<Cx::PFmla>& state_layers,
             const Cx::PFmla& xn, const Cx::PFmla& legit)
{
  state_layers.resize(0);
  state_layers.push(legit);

  Cx::PFmla visit_pf( legit );
  Cx::PFmla layer_pf( xn.pre(legit) - visit_pf );
  while (layer_pf.sat_ck()) {
    state_layers.push(layer_pf);
    visit_pf |= layer_pf;
    layer_pf = xn.pre(layer_pf) - visit_pf;
  }
  return (visit_pf.tautology_ck());
}

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
  ofilename += ".";
  ofilename += pcidx;
  oput_conflicts(conflicts, ofilename);
}

static volatile Bool done_flag = 0;

static
  void
set_done_flag (int sig)
{
  (void) sig;
  done_flag = true;
}

static
  Bool
done_ck (void* dat)
{
  (void) dat;

  if (0 == remove("kill-protocon")) {
    done_flag = true;;
  }
  else {
    errno = 0;
  }

  return done_flag;
}

static
  bool
try_known_solution(const ConflictFamily& conflicts,
                   const SynthesisCtx& synctx,
                   bool quick = true)
{
  bool good = true;
  if (synctx.done_ck())  return true;

  PartialSynthesis inst( synctx.base_inst );
  FlatSet<uint> solution( synctx.opt.known_solution );
  for (uint i = 0; i < inst.sz(); ++i) {
    inst[i].no_conflict = true;
    Set<uint> candidates( inst[i].candidates );
    candidates -= solution;
    inst[i].candidates.clear();
    inst[i].candidates.insert(inst[i].candidates.end(), solution.begin(), solution.end());
    inst[i].candidates.insert(inst[i].candidates.end(), candidates.begin(), candidates.end());
  }

  vector<uint> actions;
  bool found = false;
  if (quick) {
    if (inst.revise_actions(Set<uint>(solution), Set<uint>())) {
      found = inst.candidates.empty();
      actions = inst.actions;
    }
  }
  else {
    found = try_order_synthesis(actions, inst);
  }
  if (synctx.done_ck())  return true;
  if (found && (FlatSet<uint>(actions) == solution))
  {
    *synctx.log << "Okay, known solution can still work.\n";
  }
  else
  {
    good = false;
    if (!found)
      *synctx.log << "NO LONGER WORKING OMG\n";
    else
      *synctx.log << "WTF I SKIPPED SOME\n";

    Cx::OFileB working_of;
    working_of.open(Cx::String("working_conflicts.out.") + synctx.opt.sys_pcidx);
    working_of << conflicts;

    Cx::OFileB broken_of;
    broken_of.open(Cx::String("broken_conflicts.out.") + synctx.opt.sys_pcidx);
    broken_of << synctx.conflicts;
  }
  return good;
}

  bool
initialize_conflicts(ConflictFamily& conflicts,
                     Cx::Table< Cx::FlatSet<uint> >& flat_conflicts,
                     const ProtoconOpt& exec_opt,
                     const AddConvergenceOpt& global_opt,
                     bool do_output)
{
  if (!!exec_opt.conflicts_xfilepath)
  {
    Cx::XFileB conflicts_xf;
    conflicts_xf.open(exec_opt.conflicts_xfilepath);
    conflicts_xf >> conflicts;
    if (!conflicts_xf.good()) {
      DBog1( "Bad read from conflicts file: %s", exec_opt.conflicts_xfilepath.cstr() );
      return false;
    }
    conflicts.trim(global_opt.max_conflict_sz);
    if (do_output) {
      conflicts.oput_conflict_sizes(DBogOF);
    }
  }

  if (exec_opt.task != ProtoconOpt::MinimizeConflictsTask)
  {}
  else if (exec_opt.conflict_order == ProtoconOpt::RandomOrder)
  {
    conflicts.all_conflicts(flat_conflicts);
    Cx::URandom urandom;
    urandom.use_system_urandom(global_opt.system_urandom);
    urandom.shuffle(&flat_conflicts[0], flat_conflicts.sz());
  }
  else
  {
    conflicts.all_conflicts(flat_conflicts);
    Cx::Table< Cx::Table< FlatSet<uint> > > sized_conflicts;
    for (uint i = 0; i < flat_conflicts.sz(); ++i) {
      uint sz = flat_conflicts[i].sz();
      while (sz >= sized_conflicts.sz()) {
        sized_conflicts.grow1();
      }
      sized_conflicts[sz].push(flat_conflicts[i]);
    }
    flat_conflicts.clear();
    if (exec_opt.conflict_order == ProtoconOpt::LoHiOrder) {
      for (uint i = 0; i < sized_conflicts.sz(); ++i) {
        for (uint j = 0; j < sized_conflicts[i].sz(); ++j) {
          flat_conflicts.push(sized_conflicts[i][j]);
        }
      }
    }
    else if (exec_opt.conflict_order == ProtoconOpt::HiLoOrder) {
      for (uint i = sized_conflicts.sz(); i > 0;) {
        --i;
        for (uint j = 0; j < sized_conflicts[i].sz(); ++j) {
          flat_conflicts.push(sized_conflicts[i][j]);
        }
      }
    }
  }
  return true;
}

  bool
stabilization_search(vector<uint>& ret_actions,
                     const ProtoconFileOpt& infile_opt,
                     const ProtoconOpt& exec_opt,
                     const AddConvergenceOpt& global_opt)
{
  bool solution_found = false;
  uint NPcs = 0;
  ConflictFamily conflicts;
  Cx::Table< FlatSet<uint> > flat_conflicts;
  const bool try_known_solution_ck = !global_opt.known_solution.empty();

  signal(SIGINT, set_done_flag);
  signal(SIGTERM, set_done_flag);

  if (!initialize_conflicts(conflicts, flat_conflicts, exec_opt, global_opt, true)) {
    return false;
  }

#ifdef _OPENMP
  if (global_opt.search_method == global_opt.SerialBacktrackSearch)
    omp_set_num_threads(1);
  if (exec_opt.task == ProtoconOpt::VerifyTask && exec_opt.xfilepaths.sz()==1)
    omp_set_num_threads(1);
#endif

#pragma omp parallel shared(done_flag,NPcs,solution_found,ret_actions,conflicts,flat_conflicts)
  {
  Sign good = 1;
  AddConvergenceOpt opt(global_opt);
  uint PcIdx;
  Cx::OFileB log_ofile;
#pragma omp critical
  {
    PcIdx = NPcs;
    ++ NPcs;
  }

#pragma omp barrier
  opt.sys_pcidx = PcIdx;
  opt.sys_npcs = NPcs;

  if (!!exec_opt.log_ofilename) {
    Cx::String ofilename( exec_opt.log_ofilename );
    ofilename += ".";
    ofilename += PcIdx;
    log_ofile.open(ofilename);
    opt.log = &log_ofile;
  }
  else if (NPcs > 1) {
    opt.log = &Cx::OFile::null();
  }
  //opt.log = &DBogOF;
  //opt.verify_found = false;


  Xn::Sys sys;
  DoLegit(good, "reading file")
  {
    if (exec_opt.task != ProtoconOpt::VerifyTask)
      good = ReadProtoconFile(sys, infile_opt);
  }

  Cx::LgTable<Xn::Sys> systems;
  SynthesisCtx synctx( PcIdx, NPcs );

  synctx.conflicts = conflicts;

  DoLegit(good, "initialization")
  {
    if (exec_opt.task != ProtoconOpt::VerifyTask)
      good = synctx.init(sys, opt);
  }

  PartialSynthesis& synlvl = synctx.base_inst;

  synctx.done_ck_fn = done_ck;

  Cx::Table< Cx::Table<uint> > act_layers;
  if (opt.search_method == opt.RankShuffleSearch)
  {
    DoLegit(good, "ranking actions")
      good =
      rank_actions (act_layers, sys.topology,
                    synlvl.candidates,
                    synlvl.hi_xn,
                    synlvl.hi_invariant);
  }

  if (exec_opt.task != ProtoconOpt::VerifyTask)
  for (uint i = 1; good && i < exec_opt.params.sz(); ++i) {
    ProtoconFileOpt param_infile_opt = infile_opt;
    param_infile_opt.constant_map = exec_opt.params[i].constant_map;

    Xn::Sys& param_sys = systems.grow1();
    param_sys.topology.pfmla_ctx.use_context_of(sys.topology.pfmla_ctx);
    param_sys.topology.lightweight = !exec_opt.params[i].partial_ck();
    DoLegit(good, "reading param file")
      good = ReadProtoconFile(param_sys, param_infile_opt);
    DoLegit(good, "add param sys")
      good = synctx.add(param_sys);
  }

  for (uint i = 0; good && i < exec_opt.params.sz(); ++i) {
    synlvl[i].no_conflict = !exec_opt.params[i].conflict_ck();
    synlvl[i].no_partial = !exec_opt.params[i].partial_ck();
  }

  if (!good)
  {
    set_done_flag (1);
#pragma omp flush (done_flag)
  }

#pragma omp master
  if (try_known_solution_ck &&
      !try_known_solution (conflicts, synctx))
  {
    *opt.log << "Conflicts are inconsistent!" << opt.log->endl();
    set_done_flag (1);
  }
#pragma omp barrier
#pragma omp critical (DBog)
  DBog1( "BEGIN! %u", PcIdx );

  if (exec_opt.task == ProtoconOpt::VerifyTask)
  {
#pragma omp for schedule(dynamic)
    for (uint i = 0; i < exec_opt.xfilepaths.sz(); ++i) {
      if (synctx.done_ck())  continue;
      Xn::Sys sys;
      ProtoconFileOpt verif_infile_opt( infile_opt );
      verif_infile_opt.file_path = exec_opt.xfilepaths[i].cstr();
      *opt.log << "VERIFYING: " << verif_infile_opt.file_path << opt.log->endl();
      const bool lightweight = !exec_opt.conflicts_ofilepath;
      sys.topology.lightweight = lightweight;
      if (ReadProtoconFile(sys, verif_infile_opt)) {
        StabilizationCkInfo info;
        info.find_livelock_actions = lightweight;
        info.count_convergence_steps = exec_opt.count_convergence_steps;
        if (stabilization_ck(*opt.log, sys, &info)) {
          solution_found = true;
          ret_actions = sys.actions;
          *opt.log << "System is stabilizing." << opt.log->endl();

          if (!!exec_opt.ofilepath) {
            Cx::String filepath( exec_opt.ofilepath + "." + i );
            *opt.log << "Writing system to: " << filepath  << opt.log->endl();
            Cx::OFileB ofb;
            ofb.open(filepath);
            oput_protocon_file(ofb, sys, exec_opt.use_espresso, sys.actions);
          }
        }
        else {
          *opt.log << "System NOT stabilizing." << opt.log->endl();
          if (!lightweight && info.livelock_exists) {
            //synctx.conflicts.add_conflict(FlatSet<uint>(sys.actions));
            synctx.conflicts.add_conflict(info.livelock_actions);
          }
        }
      }
    }

#pragma omp critical (DBog)
    {
      conflicts.add_conflicts(synctx.conflicts);
      synctx.conflicts = conflicts;
    }
    synctx.conflicts.oput_conflict_sizes(*opt.log);
  }
  if (exec_opt.task == ProtoconOpt::MinimizeConflictsTask)
  {
#pragma omp for schedule(dynamic)
    for (uint conflict_idx = 0; conflict_idx < flat_conflicts.sz(); ++conflict_idx) {
      uint old_sz = flat_conflicts[conflict_idx].sz();
      if (!synctx.done_ck() && old_sz > 1) {
        *opt.log
          << "pcidx:" << PcIdx
          << " conflict:" << conflict_idx << "/" << flat_conflicts.sz()
          << " sz:" << old_sz
          << opt.log->endl();

        uint new_sz =
          synlvl.add_small_conflict_set(flat_conflicts[conflict_idx]);

        *opt.log
          << "DONE: pcidx:" << PcIdx
          << " conflict:" << conflict_idx << "/" << flat_conflicts.sz()
          << " old_sz:" << old_sz << " new_sz:" << new_sz
          << opt.log->endl();
      }
    }

#pragma omp critical (DBog)
    {
      conflicts.add_conflicts(synctx.conflicts);
      synctx.conflicts = conflicts;
    }
    synctx.conflicts.oput_conflict_sizes(*opt.log);
  }

  vector<uint> actions;
  if (exec_opt.task == ProtoconOpt::SearchTask)
  for (uint trial_idx = 0; !synctx.done_ck() && (opt.ntrials == 0 || trial_idx < opt.ntrials); ++trial_idx)
  {
    bool found = false;
    if (opt.search_method == opt.RankShuffleSearch)
    {
      PartialSynthesis tape( synlvl );
      vector<uint>& candidates = tape.candidates;
      candidates.clear();
      for (uint i = 0; i < act_layers.sz(); ++i) {
        uint off = candidates.size();
        for (uint j = 0; j < act_layers[i].sz(); ++j) {
          candidates.push_back(act_layers[i][j]);
        }
        synctx.urandom.shuffle(&candidates[off], act_layers[i].sz());
      }
      found = try_order_synthesis(actions, tape);
    }
    else
    {
      found = AddConvergence(actions, synlvl, opt);
    }

#pragma omp critical (DBog)
    {
    if (synctx.done_ck())
    {}
    else if (found)
    {
      bool count_solution = true;
      if (opt.solution_as_conflict) {
        FlatSet<uint> flat_actions( actions );
        if (conflicts.conflict_ck(flat_actions)) {
          count_solution = false;
        }
        else {
          conflicts.add_conflict(flat_actions);
        }
      }

      if (!global_opt.try_all) {
        set_done_flag (1);
      }
      else if (!!exec_opt.ofilepath && count_solution) {
        Cx::OFileB ofb;
        ofb.open(exec_opt.ofilepath + "." + PcIdx + "." + trial_idx);
        oput_protocon_file (ofb, sys, exec_opt.use_espresso, actions);
      }

      solution_found = true;
      ret_actions = actions;
      *opt.log << "SOLUTION FOUND!" << opt.log->endl();
    }
    if (!synctx.done_ck() || !!exec_opt.conflicts_ofilepath || try_known_solution_ck)
    {
      if (try_known_solution_ck &&
          !try_known_solution (conflicts, synctx))
      {
        *opt.log << "pcidx:" << PcIdx
          << " broke it, trial:" << trial_idx+1 << " before merging!\n";
        set_done_flag (1);
      }
      else {
        synctx.conflicts.add_conflicts(conflicts);

        if (try_known_solution_ck &&
            !try_known_solution (conflicts, synctx))
        {
          *opt.log << "pcidx:" << PcIdx
            << " broke it, trial:" << trial_idx+1 << " after merging!\n";
          set_done_flag (1);
        }
      }

      synctx.conflicts.trim(global_opt.max_conflict_sz);
      if (!synctx.conflicts.sat_ck())
        set_done_flag (1);

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

    if (global_opt.snapshot_conflicts && !!exec_opt.conflicts_ofilepath)
      oput_conflicts (synctx.conflicts, exec_opt.conflicts_ofilepath, PcIdx);

    if (!synctx.done_ck()) {
      Set<uint> impossible( synctx.conflicts.impossible_set );
      impossible &= Set<uint>(synlvl.candidates);
      if (!impossible.empty())
        synlvl.revise_actions(Set<uint>(), impossible);
    }

    //check_conflict_sets(conflict_sets);
  }
  }

  conflicts.trim(global_opt.max_conflict_sz);
  if (!!exec_opt.conflicts_ofilepath)
    oput_conflicts (conflicts, exec_opt.conflicts_ofilepath);

  if (global_opt.snapshot_conflicts && !!exec_opt.conflicts_ofilepath)
  {
    for (uint i = 0; i < NPcs; ++i) {
      Cx::String ofilename( exec_opt.conflicts_ofilepath );
      ofilename += ".";
      ofilename += i;
      remove(ofilename.cstr());
    }
  }

  signal(SIGINT, SIG_DFL);
  signal(SIGTERM, SIG_DFL);
  return solution_found;
}

