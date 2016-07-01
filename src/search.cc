
#include "search.hh"
#include "xnsys.hh"
#include <algorithm>

#include "cx/urandom.hh"
#include "cx/fileb.hh"
#include "opt.hh"
#include "prot-xfile.hh"
#include "prot-ofile.hh"
#include "stabilization.hh"
#include "synthesis.hh"
#include <signal.h>
#include <errno.h>

#ifdef _OPENMP
#include <omp.h>
#endif

#include "namespace.hh"

static bool
verify_solutions(const PartialSynthesis& inst, StabilizationCkInfo* info, uint* ret_nlayers_sum = 0)
{
  if (ret_nlayers_sum)
    *ret_nlayers_sum = 0;
  for (uint i = 0; i < inst.sz(); ++i) {
    if (!inst[i].no_partial)
      continue;
    *inst.log << "Verifying solution for system " << i << "..." << inst.log->endl();
    if (!stabilization_ck(*inst[i].log, *inst[i].ctx->systems[i], inst[i].stabilization_opt(),
                          inst[i].actions, info))
    {
      if (i == inst.sz()-1 && info && info->livelock_exists && !!inst.ctx->opt.livelock_ofilepath) {
        Cx::OFileB ofb;
        ofb.open(inst.ctx->opt.livelock_ofilepath + "." + inst.ctx->opt.sys_pcidx + "." + inst.ctx->opt.n_livelock_ofiles++);
        oput_protocon_file(ofb, *inst.ctx->systems[i], inst[i].actions,
                           false, "livelock");
      }
      *inst[i].log << "Solution was NOT self-stabilizing." << inst[i].log->endl();
      return false;
    }
    if (info && ret_nlayers_sum) {
      // Don't count these.
      //*ret_nlayers_sum += info->nlayers;
      *ret_nlayers_sum += 1;
    }
  }
  for (uint i = 0; i < inst.sz(); ++i) {
    if (inst[i].no_partial || !inst.ctx->opt.verify_found)
      continue;
    *inst.log << "Verifying solution for system " << i << "..." << inst.log->endl();
    if (!stabilization_ck(*inst[i].log, *inst[i].ctx->systems[i],
                          inst[i].stabilization_opt(), inst[i].actions, info))
    {
      *inst[i].log << "Solution was NOT self-stabilizing." << inst[i].log->endl();
      return false;
    }
    if (info && ret_nlayers_sum) {
      *ret_nlayers_sum += info->nlayers;
    }
  }
  return true;
}

/**
 * Add stabilization to a protocol.
 * The system will therefore be self-stabilizing.
 * This is the recursive function.
 *
 * \return  True iff convergence could be added.
 */
  bool
AddStabilization(vector<uint>& ret_actions,
                 PartialSynthesis& base_partial,
                 const AddConvergenceOpt& opt)
{
  LgTable<PartialSynthesis> bt_stack;
  SynthesisCtx& synctx = *base_partial.ctx;

  base_partial.bt_level = 0;
  base_partial.failed_bt_level = 0;
  bt_stack.push(base_partial);
  uint stack_idx = 0;
  uint nlayers_sum = 0;

  if (synctx.conflicts.conflict_ck(FlatSet<uint>(base_partial.actions))) {
    synctx.conflicts.add_conflict(FlatSet<uint>());
    return false;
  }

  while (true) {
    // This is used for an assertion at the end of this loop,
    // but the sum can be updated be updated by other processes.
    const uint old_optimal_nlayers_sum = synctx.optimal_nlayers_sum;

    PartialSynthesis& partial = bt_stack[stack_idx];
    if (synctx.done_ck()) {
      base_partial.failed_bt_level = partial.failed_bt_level;
      return false;
    }

    if (opt.max_depth > 0 && partial.bt_level >= opt.max_depth) {
      base_partial.failed_bt_level = opt.max_depth;
      return false;
    }

    if (!partial.deadlocks_ck()) {
      StabilizationCkInfo info;
      bool backtrack = false;
      if (verify_solutions(partial, &info, &nlayers_sum)) {
        if (synctx.optimal_nlayers_sum == 0 || nlayers_sum < synctx.optimal_nlayers_sum) {
          break;
        }
        backtrack = true;
        *partial.log << "SUBOPTIMAL (exceeding best known number of convergence layers: "
          << nlayers_sum << " >= " << synctx.optimal_nlayers_sum << ")" << partial.log->endl();
      }

      if (info.livelock_exists) {
        backtrack = true;
      }

      if (!backtrack && !partial.candidates_ck()) {
        return false;
      }

      if (backtrack) {
        *partial.log << "backtrack from lvl:" << partial.bt_level << partial.log->endl();
        partial.add_small_conflict_set(partial.picks);
        if (info.livelock_exists && info.find_livelock_actions) {
          partial.ctx->conflicts.add_conflict(info.livelock_actions);
        }
        stack_idx = decmod(stack_idx, 1, bt_stack.sz());
        if (bt_stack[stack_idx].bt_level >= partial.bt_level) {
          base_partial.failed_bt_level = bt_stack[stack_idx].bt_level;
          return false;
        }
        continue;
      }
    }

    // Pick the action.
    uint actidx = 0;
    if (!PickActionMRV(actidx, partial, opt)) {
      DBog0("Cannot resolve all deadlocks!");
      partial.add_small_conflict_set(partial.picks);
      return false;
    }

    uint next_idx;
    if (opt.max_height == 0 || bt_stack.sz() <= opt.max_height) {
      next_idx = stack_idx + 1;
      if (next_idx == bt_stack.sz())
        bt_stack.push(PartialSynthesis(&synctx));
    }
    else {
      next_idx = incmod(stack_idx, 1, bt_stack.sz());
    }
    PartialSynthesis& next = bt_stack[next_idx];
    next = partial;
    next.godeeper1();
    next.failed_bt_level = next.bt_level;

    if (next.pick_action(actidx))
    {
      stack_idx = next_idx;
      continue;
    }

    if (synctx.done_ck()) {
      base_partial.failed_bt_level = partial.failed_bt_level;
      return false;
    }

    while (!bt_stack[stack_idx].revise_actions(Set<uint>(), Set<uint>(actidx), &nlayers_sum))
    {
      PartialSynthesis& partial = bt_stack[stack_idx];
      *partial.log << "backtrack from lvl:" << partial.bt_level << partial.log->endl();
      partial.add_small_conflict_set(partial.picks);

      stack_idx = decmod(stack_idx, 1, bt_stack.sz());

      if (bt_stack[stack_idx].bt_level >= partial.bt_level) {
        base_partial.failed_bt_level = bt_stack[stack_idx].bt_level;
        return false;
      }

      if (synctx.done_ck()) {
        base_partial.failed_bt_level = partial.failed_bt_level;
        return false;
      }
      actidx = partial.picks.top();
    }
    if (old_optimal_nlayers_sum > 0) {
      Claim2( nlayers_sum ,<, old_optimal_nlayers_sum );
    }
  }
  PartialSynthesis& partial = bt_stack[stack_idx];
  for (uint i = 0; i < partial.sz(); ++i) {
    Claim(!partial[i].deadlockPF.sat_ck());
  }
  ret_actions = partial.actions;
  Claim2( nlayers_sum ,>, 0 );
  synctx.optimal_nlayers_sum = nlayers_sum;
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
AddStabilization(Xn::Sys& sys, const AddConvergenceOpt& opt)
{
  SynthesisCtx synctx;
  StabilizationOpt stabilization_opt;
  if (!synctx.init(opt))
    return false;

  if (!synctx.add(sys, stabilization_opt))
    return false;

  PartialSynthesis& partial = synctx.base_partial;

  if (!partial.revise_actions(Set<uint>(sys.actions), synctx.conflicts.impossible_set))
    return false;

  vector<uint> ret_actions;
  bool found = AddStabilization(ret_actions, partial, opt);
  if (!found)  return false;

  sys.actions = ret_actions;
  return true;
}


  void
check_conflict_sets(const LgTable< Set<uint> >& conflict_sets)
{
  for (zuint i = conflict_sets.begidx();
       i != SIZE_MAX;
       i = conflict_sets.nextidx(i))
  {
    const Set<uint>& a = conflict_sets[i];
    for (zuint j = conflict_sets.nextidx(i);
         j != SIZE_MAX;
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
rank_states (Table<P::Fmla>& state_layers,
             const X::Fmla& xn, const P::Fmla& legit)
{
  state_layers.resize(0);
  state_layers.push(legit);

  P::Fmla visit_pf( legit );
  P::Fmla layer_pf( xn.pre(legit) - visit_pf );
  while (layer_pf.sat_ck()) {
    state_layers.push(layer_pf);
    visit_pf |= layer_pf;
    layer_pf = xn.pre(layer_pf) - visit_pf;
  }
  return (visit_pf.tautology_ck());
}

  bool
rank_actions (Table< Table<uint> >& act_layers,
              const Xn::Net& topo,
              const vector<uint>& candidates,
              const X::Fmla& xn,
              const P::Fmla& legit)
{
  Table<P::Fmla> state_layers;
  if (!rank_states (state_layers, xn, legit))
    return false;

  act_layers.resize(state_layers.sz()+1);
  for (uint i = 0; i < candidates.size(); ++i) {
    const uint actidx = candidates[i];
    const X::Fmla& act_pf = topo.action_pfmla(actidx);
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
oput_conflicts (const ConflictFamily& conflicts, const String& ofilename)
{
  Cx::OFileB conflicts_of;
  conflicts_of.open(ofilename.cstr());
  conflicts_of << conflicts;
}

  void
oput_conflicts (const ConflictFamily& conflicts, String ofilename, uint pcidx)
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
    done_flag = true;
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

  PartialSynthesis inst( synctx.base_partial );
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
      *synctx.log << "NO LONGER WORKING\n";
    else
      *synctx.log << "I SKIPPED SOME\n";

    Cx::OFileB working_of;
    working_of.open(String("working_conflicts.out.") + synctx.opt.sys_pcidx);
    working_of << conflicts;

    Cx::OFileB broken_of;
    broken_of.open(String("broken_conflicts.out.") + synctx.opt.sys_pcidx);
    broken_of << synctx.conflicts;
  }
  return good;
}

  bool
initialize_conflicts(ConflictFamily& conflicts,
                     Table< FlatSet<uint> >& flat_conflicts,
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
    URandom urandom;
    urandom.use_system_urandom(global_opt.system_urandom);
    urandom.shuffle(&flat_conflicts[0], flat_conflicts.sz());
  }
  else
  {
    conflicts.all_conflicts(flat_conflicts);
    Table< Table< FlatSet<uint> > > sized_conflicts;
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
stabilization_search_init
  (SynthesisCtx& synctx,
   Xn::Sys& sys,
   LgTable<Xn::Sys>& systems,
   Cx::OFileB& log_ofile,
   AddConvergenceOpt& opt,
   const ProtoconFileOpt& infile_opt,
   const ProtoconOpt& exec_opt,
   Table< Table<uint> >& act_layers
   )
{
  DeclLegit( good );

  if (!!exec_opt.log_ofilename) {
    String ofilename( exec_opt.log_ofilename );
    ofilename += ".";
    ofilename += opt.sys_pcidx;
    log_ofile.open(ofilename);
    opt.log = &log_ofile;
  }
  else if (opt.sys_npcs > 1) {
    opt.log = &OFile::null();
  }


  DoLegit("reading file")
  {
    if (exec_opt.task != ProtoconOpt::VerifyTask)
      good = ReadProtoconFile(sys, infile_opt);
  }

  DoLegit("Repeated variable references in all processes!")
  {
    for (uint i = 0; i < sys.topology.pc_symms.sz(); ++i) {
      const Xn::PcSymm& pc_symm = sys.topology.pc_symms[i];
      uint pcidx = 0;
      if (pc_symm.membs.sz() > 0 && !pc_symm.representative(&pcidx)) {
        String msg;
        msg << "Every process "
          << pc_symm.spec->name << "[" << pc_symm.spec->idx_name << "]"
          << " has repeated variable references!";
        DBog0( msg.ccstr() );
        good = 0;
      }
    }
    if (!good) {
      DBog0("`- Try placing the -def flag AFTER the -x flag.");
      DBog0("`- If that doesn't work, the input system needs to be larger or");
      DBog0("`- you need to remove duplicate variable references after read/write keywords.");
      DBog0("`- Also recall that write access implies read access.");
    }
  }

  DoLegit("initialization")
  {
    if (exec_opt.task != ProtoconOpt::VerifyTask)
      good = synctx.init(opt);
  }

  if (exec_opt.task != ProtoconOpt::VerifyTask)
  for (uint i = 0; good && i < exec_opt.instances.sz(); ++i) {
    ProtoconFileOpt param_infile_opt = infile_opt;
    param_infile_opt.constant_map = exec_opt.instances[i].constant_map;

    Xn::Sys& param_sys = systems.grow1();
    param_sys.topology.pfmla_ctx.use_context_of(sys.topology.pfmla_ctx);
    param_sys.topology.lightweight = !exec_opt.instances[i].partial_ck();
    DoLegitLine("reading param file")
      ReadProtoconFile(param_sys, param_infile_opt);
    DoLegitLine("add param sys")
      synctx.add(param_sys, exec_opt.instances[i].stabilization_opt);
  }

  DoLegit("The -def flag changes variable domains, put it before -x")
  {
    for (uint i = 0; i < sys.topology.pc_symms.sz(); ++i) {
      const Xn::PcSymm& a = sys.topology.pc_symms[i];
      const Xn::PcSymm& b = systems[0].topology.pc_symms[i];
      if (!a.dom_equiv_ck(b))
        good = 0;
    }
  }

  DoLegit("A -param flag changes variable domains, don't do this")
  {
    for (uint sysidx = 1; sysidx < systems.sz(); ++sysidx) {
      for (uint i = 0; i < sys.topology.pc_symms.sz(); ++i) {
        const Xn::PcSymm& a = sys.topology.pc_symms[i];
        const Xn::PcSymm& b = systems[sysidx].topology.pc_symms[i];
        if (!a.dom_equiv_ck(b))
          good = 0;
      }
    }
  }


  PartialSynthesis& synlvl = synctx.base_partial;

  for (uint i = 0; good && i < exec_opt.instances.sz(); ++i) {
    synlvl[i].no_conflict = !exec_opt.instances[i].conflict_ck();
    synlvl[i].no_partial = !exec_opt.instances[i].partial_ck();
  }

  if (exec_opt.task != ProtoconOpt::VerifyTask)
  DoLegit( "initializing actions" )
  {
    Set<uint> act_set(sys.actions);
    good = synlvl.revise_actions(act_set, synctx.conflicts.impossible_set);
    if (!good) {
      DBog0("No actions apply!");
    }
  }

  if (opt.search_method == opt.RankShuffleSearch)
  {
    // TODO: Figure some way to incorporate all systems.
    for (uint i = 0; i < 1 /*synlvl.sz()*/; ++i) {
      act_layers.clear();
      DoLegitLine("ranking actions")
        rank_actions (act_layers, systems[i].topology,
                      synlvl[i].candidates,
                      synlvl[i].hi_xn,
                      synlvl[i].hi_invariant);
    }
  }

  return !!good;
}


void
  multi_verify_stabilization
( uint i,
  SynthesisCtx& synctx,
  vector<uint>& ret_actions,
  bool& solution_found,
  const ProtoconFileOpt& infile_opt,
  const ProtoconOpt& exec_opt,
  AddConvergenceOpt& opt
)
{
  Xn::Sys sys;
  ProtoconFileOpt verif_infile_opt( infile_opt );
  verif_infile_opt.constant_map = exec_opt.instances[0].constant_map;
  const String& xfilepath = exec_opt.xfilepaths[i];
  if (xfilepath != exec_opt.xfilepath) {
    verif_infile_opt.text.moveq
      (textfile_AlphaTab (0, xfilepath.cstr()));
  }
  *opt.log << "VERIFYING: " << xfilepath << opt.log->endl();
  const bool lightweight = !exec_opt.conflicts_ofilepath;
  sys.topology.lightweight = lightweight;
  if (ReadProtoconFile(sys, verif_infile_opt)) {
    StabilizationCkInfo info;
    info.find_livelock_actions = !lightweight;
    if (stabilization_ck(*opt.log, sys, exec_opt.instances[0].stabilization_opt, &info)) {
      solution_found = true;
      ret_actions = sys.actions;
      *opt.log << "System is stabilizing." << opt.log->endl();

      if (!!exec_opt.ofilepath) {
        String filepath( exec_opt.ofilepath + "." + i );
        *opt.log << "Writing system to: " << filepath  << opt.log->endl();
        Cx::OFileB ofb;
        ofb.open(filepath);
        oput_protocon_file(ofb, sys, sys.actions,
                           exec_opt.use_espresso,
                           exec_opt.argline.ccstr());
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
  else {
    *opt.log << "Error reading file: " << xfilepath << opt.log->endl();
  }
}


  bool
stabilization_search(vector<uint>& ret_actions,
                     const ProtoconFileOpt& infile_opt,
                     const ProtoconOpt& exec_opt,
                     const AddConvergenceOpt& global_opt)
{
  bool solution_found = false;
  uint solution_nlayers_sum = 0;
  uint NPcs = 0;
  ConflictFamily conflicts;
  Table< FlatSet<uint> > flat_conflicts;
  const bool try_known_solution_ck = !global_opt.known_solution.empty();

  signal(SIGINT, set_done_flag);
  signal(SIGTERM, set_done_flag);

  if (!initialize_conflicts(conflicts, flat_conflicts, exec_opt, global_opt, true)) {
    return false;
  }

#ifdef _OPENMP
  if (exec_opt.nparallel != 0)
    omp_set_num_threads(exec_opt.nparallel);
  if (exec_opt.task == ProtoconOpt::VerifyTask && exec_opt.xfilepaths.sz()==1)
    omp_set_num_threads(1);
#endif

#pragma omp parallel shared(done_flag,NPcs,solution_found,solution_nlayers_sum,\
                            ret_actions,conflicts,flat_conflicts)
  {
  DeclLegit( good );
  AddConvergenceOpt opt(global_opt);
  uint PcIdx;
  Cx::OFileB log_ofile;
#pragma omp critical
  {
    PcIdx = NPcs;
    ++ NPcs;
  }

#pragma omp barrier

  //opt.log = &DBogOF;
  //opt.verify_found = false;

  opt.sys_pcidx = PcIdx;
  opt.sys_npcs = NPcs;

  Xn::Sys sys;
  LgTable<Xn::Sys> systems;
  SynthesisCtx synctx( PcIdx, NPcs );
  synctx.conflicts = conflicts;

  Table< Table<uint> > act_layers;

  DoLegitLine( "init call failed" )
    stabilization_search_init
    (synctx, sys, systems, log_ofile, opt, infile_opt, exec_opt, act_layers);

  PartialSynthesis& synlvl = synctx.base_partial;
  synctx.done_ck_fn = done_ck;


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
      multi_verify_stabilization
        (i, synctx, ret_actions,
         solution_found,
         infile_opt, exec_opt, opt);
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

  if (exec_opt.task == ProtoconOpt::TestTask) {
#pragma omp barrier
    for (uint trial_idx = 0;
         !synctx.done_ck() &&
         NPcs * trial_idx + PcIdx < global_opt.solution_guesses.sz();
         ++trial_idx)
    {
      bool sat = true;
      PartialSynthesis partial( synlvl );
      const uint guess_idx = NPcs * trial_idx + PcIdx;;
      vector<uint> guess = global_opt.solution_guesses[guess_idx];
      bool subset_guess =
        global_opt.subset_solution_guesses.elem_ck(guess_idx);

      if (opt.randomize_pick) {
        synctx.urandom.shuffle(&guess[0], guess.size());
      }

      sat = sat && partial.pick_actions_separately(guess, !subset_guess);
      sat = sat && !partial.deadlocks_ck();
      vector<uint> actions;
      sat = sat && AddStabilization(actions, partial, opt);
      synctx.optimal_nlayers_sum = 0;
      if (sat) {
        Set<uint> guess_set( guess );
        Set<uint> action_set( actions );
        sat = action_set.subseteq_ck(guess_set);
#pragma omp critical (DBog)
        if (!sat) {
          DBog0( "Synthesized more actions than necessary!" );
        }
        if (sat && !subset_guess)
          sat = guess_set.subseteq_ck(action_set);
      }
#pragma omp critical (DBog)
      if (!synctx.done_ck())
      {
        if (!sat) {
          solution_found = false;
          ret_actions.clear();
          set_done_flag(1);
        }
        else if (!solution_found) {
          solution_found = true;
          ret_actions = actions;
        }
      }
    }
  }

  if (exec_opt.task == ProtoconOpt::SearchTask)
  for (uint trial_idx = 0; !synctx.done_ck() && (opt.ntrials == 0 || trial_idx < opt.ntrials); ++trial_idx)
  {
    bool found = false;
    vector<uint> actions;
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
    else if (NPcs * trial_idx + PcIdx < global_opt.solution_guesses.sz()) {
      PartialSynthesis tape( synlvl );
      if (tape.pick_actions(global_opt.solution_guesses[NPcs * trial_idx + PcIdx])) {
        found = AddStabilization(actions, tape, opt);
      }
      synlvl.failed_bt_level = tape.failed_bt_level;
    }
    else
    {
      found = AddStabilization(actions, synlvl, opt);
    }

#pragma omp critical (DBog)
    {

    if (synctx.done_ck())
    {}
    else if (found)
    {
      bool count_solution = true;
      if (opt.solution_as_conflict || global_opt.optimize_soln) {
        FlatSet<uint> flat_actions( actions );
        if (conflicts.conflict_ck(flat_actions)) {
          count_solution = false;
        }
        else {
          conflicts.add_conflict(flat_actions);
        }
      }

      if (count_solution && global_opt.optimize_soln) {
        count_solution =
          solution_nlayers_sum == 0 ||
          synctx.optimal_nlayers_sum < solution_nlayers_sum;

      }

      if (count_solution) {
        *opt.log << "SOLUTION FOUND!" << opt.log->endl();
        solution_found = true;
        ret_actions = actions;
        if (global_opt.try_all && !!exec_opt.ofilepath) {
          Cx::OFileB ofb;
          ofb.open(exec_opt.ofilepath + "." + PcIdx + "." + trial_idx);
          oput_protocon_file (ofb, sys, actions,
                              exec_opt.use_espresso,
                              exec_opt.argline.ccstr());
        }
      }

      if (!count_solution) {
      }
      else if (global_opt.optimize_soln) {
        solution_nlayers_sum = synctx.optimal_nlayers_sum;
      }
      else if (!global_opt.try_all) {
        set_done_flag (1);
      }
    }

    if (synctx.opt.optimize_soln) {
      synctx.optimal_nlayers_sum = solution_nlayers_sum;
    }
    else {
      synctx.optimal_nlayers_sum = 0;
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
        DBogOF << "pcidx:" << PcIdx << " trial:" << trial_idx+1 << " depth:" << synlvl.failed_bt_level
          << " nlayers_sum:" << solution_nlayers_sum << '\n';
      DBogOF.flush();
    }
    }

    synctx.conflicts.oput_conflict_sizes(*opt.log);
    if (opt.search_method == opt.RankShuffleSearch)
      *opt.log << "pcidx:" << PcIdx << " trial:" << trial_idx+1 << " actions:" << actions.size() << '\n';
    else
      *opt.log << "pcidx:" << PcIdx << " trial:" << trial_idx+1 << " depth:" << synlvl.failed_bt_level
        << " nlayers_sum:" << solution_nlayers_sum << '\n';
    opt.log->flush();

    if (global_opt.snapshot_conflicts && !!exec_opt.conflicts_ofilepath)
      oput_conflicts (synctx.conflicts, exec_opt.conflicts_ofilepath, PcIdx);

    if (!synctx.done_ck()) {
      Set<uint> impossible( synctx.conflicts.impossible_set );
      impossible &= Set<uint>(synlvl.candidates);
      if (!impossible.empty()) {
        if (!synlvl.revise_actions(Set<uint>(), impossible)) {
          // No solution exists.
          // Or no more solutions can be found.
          set_done_flag (1);
        }
      }
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
      String ofilename( exec_opt.conflicts_ofilepath );
      ofilename += ".";
      ofilename += i;
      remove(ofilename.cstr());
    }
  }

  signal(SIGINT, SIG_DFL);
  signal(SIGTERM, SIG_DFL);
  return solution_found;
}

END_NAMESPACE

