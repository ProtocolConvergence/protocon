
extern "C" {
#include "cx/syscx.h"
}

#include "stability.hh"
#include "pla.hh"
#include "cx/fileb.hh"
#include "ordersyn.hh"

static
  bool
VerifyStabilization(const Xn::Sys& sys, const vector<uint>& actions)
{
  Cx::OFile& of = DBogOF;
  const Xn::Net& topo = sys.topology;
  Cx::PFmla xn( false );
  of << "Building transition relation...\n";
  of.flush();
  for (uint i = 0; i < actions.size(); ++i) {
    xn |= topo.action_pfmla(actions[i]);
  }
  of << "Checking for deadlocks...\n";
  of.flush();
  if (!(~sys.invariant).subseteq_ck(xn.pre())) {
    of << "Deadlock found.\n";
    of.flush();
    return false;
  }
  of << "Finding SCCs...\n";
  of.flush();
  Cx::PFmla scc( false );
  cycle_ck(&scc, xn);
  if (!scc.subseteq_ck(sys.invariant)) {
    of << "Livelock found.\n";
    of.flush();
    return false;
  }
  of << "Calculating invariant...\n";
  of.flush();
  const Cx::PFmla& invariant =
    LegitInvariant(sys, xn, xn, &scc);
  if (!invariant.sat_ck()) {
    of << "Invariant not valid, given the protocol and behavior.\n";
    of.flush();
    return false;
  }
  of << "Checking for deadlocks in new invariant...\n";
  of.flush();
  if (!(~invariant).subseteq_ck(xn.pre())) {
    of << "Deadlock found.\n";
    of.flush();
    return false;
  }
  of << "Checking for weak convergence...\n";
  of.flush();
  if (!WeakConvergenceCk(sys, xn, invariant)) {
    of << "Weak convergence does not hold...\n";
    of.flush();
    return false;
  }
#if 0
  of << "Checking for cycles using SCC_Find...\n";
  of.flush();
  if (SCC_Find(&scc, xn, ~invariant)) {
    of << "Livelock found.\n";
    topo.oput_all_pf(of, scc);
    of.flush();
    return false;
  }
#endif
  return true;
}

static
  bool
VerifyStabilization(const Xn::Sys& sys)
{
  return VerifyStabilization(sys, sys.actions);
}


/**
 * Add convergence to a system.
 * The system will therefore be self-stabilizing.
 * This is the recursive function.
 *
 * \param sys  System definition. It is modified if convergence is added.
 * \return  True iff convergence could be added.
 */
  bool
AddConvergence(vector<uint>& retActions,
               const Xn::Sys& sys,
               StabilitySynLvl& base_lvl,
               const AddConvergenceOpt& opt)
{
  Cx::LgTable<StabilitySynLvl> bt_stack;
  StabilitySyn& synctx = *base_lvl.ctx;

  base_lvl.bt_level = 0;
  base_lvl.failed_bt_level = 0;
  bt_stack.push(base_lvl);
  uint stack_idx = 0;

  while (true) {
    StabilitySynLvl& tape = bt_stack[stack_idx];
    if (tape.candidates.empty())
      break;
    if (synctx.done && *synctx.done)
      return false;

    // Pick the action.
    uint actidx = 0;
    if (!PickActionMCV(actidx, sys, tape, opt)) {
      DBog0("Cannot resolve all deadlocks!");
      return false;
    }

    uint next_idx;
    if (!opt.random_one_shot || bt_stack.sz() < opt.bt_depth) {
      next_idx = stack_idx + 1;
      if (next_idx == bt_stack.sz())
        bt_stack.push(StabilitySynLvl(&synctx));
    }
    else {
      next_idx = incmod(stack_idx, 1, bt_stack.sz());
    }
    StabilitySynLvl& next = bt_stack[next_idx];
    next = tape;
    next.bt_level += 1;
    next.failed_bt_level = next.bt_level;

    if (next.pick_action(sys, actidx))
    {
      stack_idx = next_idx;
      continue;
    }

    if (synctx.done && *synctx.done)
      return false;

    if (tape.revise_actions(sys, Set<uint>(), Set<uint>(actidx)))
      continue;

    if (tape.bt_dbog) {
      DBog1("backtrack from lvl %u", tape.bt_level);
    }
    tape.add_small_conflict_set(sys, tape.picks);

    stack_idx = decmod(stack_idx, 1, bt_stack.sz());

    if (bt_stack[stack_idx].bt_level >= tape.bt_level) {
      base_lvl.failed_bt_level = bt_stack[stack_idx].bt_level;
      return false;
    }
  }

  StabilitySynLvl& tape = bt_stack[stack_idx];
  Claim(!tape.deadlockPF.sat_ck());

  if (opt.verify_found) {
    DBog0( "Verifying solution..." );
    if (!VerifyStabilization(sys, tape.actions)) {
      DBog0( "Solution was NOT self-stabilizing." );
      return false;
    }
  }
  retActions = tape.actions;
  return true;
}

/**
 * Initialize synthesis structures.
 */
  bool
InitStabilitySyn(StabilitySyn& synctx,
                 StabilitySynLvl& tape,
                 const Xn::Sys& sys,
                 const AddConvergenceOpt& opt)
{
  const Xn::Net& topo = sys.topology;
  synctx.opt = opt;
  synctx.base_lvl = &tape;

  for (uint pcidx = 0; pcidx < topo.pc_symms.sz(); ++pcidx)
  {
    const Xn::PcSymm& pc_symm = topo.pc_symms[pcidx];
    for (uint i = 0; i < pc_symm.pre_domsz; ++i)
    {
      Cx::String name = pc_symm.name + "@pre_enum[" + i + "]";
      uint vbl_idx =
        synctx.csp_pfmla_ctx.add_vbl(name, pc_symm.img_domsz);
      Claim2( vbl_idx ,==, pc_symm.pre_dom_offset + i );
    }

    Xn::ActSymm act;
    // Enforce self-disabling actions.
    if (false)
    for (uint actidx = 0; actidx < pc_symm.n_possible_acts; ++actidx) {
      pc_symm.action(act, actidx);
      synctx.csp_base_pfmla &=
        (synctx.csp_pfmla_ctx.vbl(act.pre_idx) != act.img_idx)
        |
        (synctx.csp_pfmla_ctx.vbl(act.pre_idx_of_img) == act.img_idx);
    }
  }

  tape.loXnRel = false;
  tape.hiXnRel = false;
  tape.csp_pfmla = synctx.csp_base_pfmla;

  bool good =
    candidate_actions(tape.candidates, sys);
  if (!good) {
    return false;
  }
  if (good && tape.candidates.size() == 0) {
    return true;
  }

  for (uint i = 0; i < tape.candidates.size(); ++i) {
    tape.hiXnRel |= topo.action_pfmla(tape.candidates[i]);
  }

  tape.deadlockPF = ~sys.invariant;
  if (sys.shadow_puppet_synthesis_ck()) {
    tape.deadlockPF |= sys.shadow_pfmla.pre();
  }

  tape.backReachPF = sys.invariant;

  RankDeadlocksMCV(tape.mcvDeadlocks,
                   sys.topology,
                   tape.candidates,
                   tape.deadlockPF);

  if (tape.mcvDeadlocks.size() < 2) {
    DBog0("Cannot resolve all deadlocks with known actions!");
    return false;
  }

  tape.bt_dbog = opt.bt_dbog;
  if (!tape.revise_actions(sys, Set<uint>(sys.actions), Set<uint>()))
  {
    DBog0("No actions apply!");
    return false;
  }

  if (tape.deadlockPF.tautology_ck(false) &&
      tape.actions.size() == sys.actions.size() &&
      tape.candidates.size() == 0)
  {
    DBog0("The given protocol is self-stabilizing.");
  }
  return good;
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
  StabilitySyn synctx;
  StabilitySynLvl tape( &synctx );
  if (!InitStabilitySyn(synctx, tape, sys, opt))
    return false;

  vector<uint> retActions;
  bool found = AddConvergence(retActions, sys, tape, opt);
  if (!found)  return false;

  sys.actions = retActions;
  return true;
}

/** Execute me now!*/
int main(int argc, char** argv)
{
  enum ProblemInstance {
    FromFileInstance,
    ThreeColoringRingInstance,
    TwoColoringRingInstance,
    MaximalMatchingInstance,
    SumNotTwoInstance,
    AgreementRingInstance,
    NProblemInstances
  } problem = NProblemInstances;
  int argi = (init_sysCx (&argc, &argv), 1);
  uint npcs = 4;
  AddConvergenceOpt opt;
  const char* modelFilePath = 0;
  ProtoconFileOpt infile_opt;
  const char* outfile_path = 0;
  bool verify = false;

  // Use to disable picking only actions which resolve deadlocks
  // by making them backwards reachable from the invariant.
  opt.pickBackReach = false;
  // Use to disable process ordering.
  //opt.nicePolicy = opt.NilNice;
  // Use to change picking method.
  //opt.pickMethod = opt.GreedyPick;
  //opt.pickMethod = opt.QuickPick;
  //opt.pickMethod = opt.LCVHeavyPick;
  opt.pickMethod = opt.LCVLitePick;

  while (pfxeq_cstr ("-", argv[argi])) {
    const char* arg = argv[argi++];
    if (eq_cstr (arg, "-model")) {
      modelFilePath = argv[argi++];
      if (!modelFilePath){
        DBog0("No path given!!!!");
      }
    }
    else if (eq_cstr (arg, "-random")) {
      opt.search_method = opt.RandomBacktrackSearch;
    }
    else if (eq_cstr (arg, "-rankshuffle") || eq_cstr (arg, "-rank-shuffle")) {
      opt.search_method = opt.RankShuffleSearch;
    }
    else if (eq_cstr (arg, "-test")) {
      DBog0( "Running tests..." );
      Test();
      DBog0( "Done." );
      lose_sysCx ();
      return 0;
    }
    else if (eq_cstr (arg, "-def")) {
      if (argi + 1 >= argc) {
        failout_sysCx("2 arguments needed for -def.\n");
      }
      const char* key = argv[argi++];
      const char* val = argv[argi++];
      uint x = 0;
      if (!xget_uint_cstr (&x, val))
        failout_sysCx("Argument Usage: -def KEY VAL\nWhere VAL is an unsigned integer!");
      infile_opt.constant_map[key] = x;
    }
    else if (eq_cstr (arg, "-x")) {
      DBog0("Problem: From File");
      problem = FromFileInstance;
      infile_opt.file_path = argv[argi++];
      if (!infile_opt.file_path) {
        failout_sysCx("Not enuff arguments.\n");
      }
    }
    else if (eq_cstr (arg, "-o")) {
      outfile_path = argv[argi++];
      if (!outfile_path) {
        failout_sysCx("Not enuff arguments.\n");
      }
    }
    else if (eq_cstr (arg, "-ntrials")) {
      if (!xget_uint_cstr (&opt.ntrials, argv[argi++])) {
        failout_sysCx("Argument Usage: -ntrials N");
      }
    }
    else if (eq_cstr (arg, "-try-all")) {
      opt.try_all = true;
    }
    else if (eq_cstr (arg, "-x-conflicts")) {
      opt.conflicts_xfilename = argv[argi++];
    }
    else if (eq_cstr (arg, "-o-conflicts")) {
      opt.conflicts_ofilename = argv[argi++];
    }
    else if (eq_cstr (arg, "-snapshot-conflicts")) {
      opt.snapshot_conflicts = true;
    }
    else if (eq_cstr (arg, "-max-conflict")) {
      if (!xget_uint_cstr (&opt.max_conflict_sz, argv[argi++])) {
        failout_sysCx("Argument Usage: -max-conflict N");
      }
    }
    else if (eq_cstr (arg, "-verify")) {
      verify = true;
    }
    else if (eq_cstr (arg, "-pick")) {
      const char* method = argv[argi++];
      if (eq_cstr (method, "greedy")) {
        opt.pickMethod = opt.GreedyPick;
      }
      else if (eq_cstr (method, "lcv")) {
        opt.pickMethod = opt.LCVLitePick;
      }
      else if (eq_cstr (method, "quick")) {
        opt.pickMethod = opt.QuickPick;
      }
      else {
        failout_sysCx("Argument Usage: -pick [greedy|lcv|quick]");
      }
    }
    else {
      failout_sysCx(arg);
    }
  }

  if (problem == FromFileInstance) {
  }
  else if (argi < argc) {
    if (false) {
    }
    else if (string(argv[argi]) == "3-coloring") {
      DBog0("Problem: 3-Coloring on Bidirectional Ring");
      problem = ThreeColoringRingInstance;
    }
    else if (string(argv[argi]) == "2-coloring") {
      DBog0("Problem: 2-Coloring on Unidirectional Ring");
      problem = TwoColoringRingInstance;
    }
    else if (string(argv[argi]) == "matching") {
      DBog0("Problem: Maximal Matching");
      problem = MaximalMatchingInstance;
    }
    else if (string(argv[argi]) == "sum-not-2") {
      DBog0("Problem: Sum-Not-2");
      problem = SumNotTwoInstance;
    }
    else if (string(argv[argi]) == "agreement") {
      DBog0("Problem: Agreement");
      problem = AgreementRingInstance;
    }
    else{
      //printf("%s: Only supported argument is \"test\".\n", argv[0]);
      failout_sysCx("No valid problem given.\n");
    }
    ++argi;

    if (argi < argc) {
      npcs = (uint) atoi(argv[argi++]);
    }
    else {
      DBog1("Using default process count: %u", npcs);
    }
  }
  else {
    failout_sysCx("No valid problem given.\n");
  }

  if (argi < argc) {
    failout_sysCx("Too many arguments!");
  }

  // Set up the chosen problem.
  Xn::Sys sys;
  switch(problem){
    case FromFileInstance:
      if (!ReadProtoconFile(sys, infile_opt))
        failout_sysCx ("");
      break;
    case ThreeColoringRingInstance:
      InstThreeColoringRing(sys, npcs);  break;
    case TwoColoringRingInstance:
      InstTwoColoringRing(sys, npcs);  break;
    case MaximalMatchingInstance:
      InstMatching(sys, npcs);  break;
    case SumNotTwoInstance:
      InstSumNot(sys, npcs, 3, 2);  break;
    case AgreementRingInstance:
      InstAgreementRing(sys, npcs);  break;
    case NProblemInstances:
    default:
      DBog0("No case for this problem instance!");
      return 1;
  }

  if (!sys.integrityCk()) {
    failout_sysCx ("Bad system definition.");
  }

  bool found = false;
  if (verify) {
    found = VerifyStabilization(sys);
  }
  else if (opt.search_method != opt.BacktrackSearch) {
    if (!infile_opt.file_path) {
      failout_sysCx ("Need to use input file with random or rank/shuffle method!");
    }
    found =
      flat_backtrack_synthesis(sys.actions, infile_opt, opt);
  }
  else {
    found = AddConvergence(sys, opt);
  }

  if (verify) {
    if (found) {
      DBog0( "Protocol is self-stabilizing!" );
    }
    else {
      DBog0( "Protocol is NOT self-stabilizing... :(" );
    }
  }
  else if (found) {
    DBog0("Solution found!");
    for (uint i = 0; i < sys.actions.size(); ++i) {
      const Xn::Net& topo = sys.topology;
      Xn::ActSymm act;
      topo.action(act, sys.actions[i]);
      //DBogOF << sys.actions[i] << ' ';
      OPut(DBogOF, act) << '\n';
    }
  }
  else {
    DBog0("No solution found...");
  }

  if (found) {
    if (modelFilePath)  {
      std::fstream of(modelFilePath,
                      std::ios::binary |
                      std::ios::out |
                      std::ios::trunc);
      OPutPromelaModel(of, sys);
      of.close();
      DBog1("Model written to \"%s\".", modelFilePath);
      DBog0("WARNING: The model is not working at this time.");
    }
    if (outfile_path)
    {
      Cx::OFileB ofb;
      ofb.open(outfile_path);
      oput_protocon_file (ofb, sys);
    }
  }
  DBogOF.flush();

  lose_sysCx ();
  return found ? 0 : 2;
}

