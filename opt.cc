
extern "C" {
#include "cx/syscx.h"
}

#include "opt.hh"
#include "synthesis.hh"
#include "pla.hh"
#include "cx/fileb.hh"
#include "search.hh"

enum ProblemInstance {
  FromFileInstance,
  ThreeColoringRingInstance,
  TwoColoringRingInstance,
  MaximalMatchingInstance,
  SumNotTwoInstance,
  AgreementRingInstance,
  NProblemInstances
};

static
  bool
handle_param_arg(ProtoconParamOpt& psys_opt, const char* arg, int& argi, int argc, char** argv)
{
  if (eq_cstr (arg, "-no-conflict")) {
    psys_opt.conflict = false;
  }
  else if (eq_cstr (arg, "-no-conflicts")) {
    psys_opt.conflict = false;
  }
  else if (eq_cstr (arg, "-synchronous")) {
    psys_opt.stabilization_opt.synchronous = true;
  }
  else if (eq_cstr (arg, "-count-convergence-layers")) {
    psys_opt.stabilization_opt.count_convergence_layers = true;
  }
  else if (eq_cstr (arg, "-max-nlayers")) {
    uint x = 0;
    if (argi >= argc) {
      failout_sysCx("1 arguments needed for -max-nlayers.\n");
    }
    arg = argv[argi++];
    if (!xget_uint_cstr (&x, arg))
      failout_sysCx("Argument Usage: -max-nlayers NLAYERS\nWhere NLAYERS is an unsigned integer!");
    psys_opt.stabilization_opt.max_nlayers = x;
  }
  else {
    return false;
  }
  return true;
}

static
  bool
parse_param(ProtoconOpt& opt, int& argi, int argc, char** argv)
{
  ProtoconParamOpt& psys_opt = opt.params.grow1();
  psys_opt = opt.params[0];
  if (!eq_cstr(argv[argi], "(") &&
      !eq_cstr(argv[argi], "[")) {
    if (argi + 1 >= argc) {
      failout_sysCx("2 arguments needed for -param.\n");
    }
    const char* key = argv[argi++];
    const char* val = argv[argi++];
    uint x = 0;
    if (!xget_uint_cstr (&x, val))
      failout_sysCx("Argument Usage: -param KEY VAL\nWhere VAL is an unsigned integer!");
    psys_opt.constant_map[key] = x;
    return true;
  }
  ++ argi;

  while (argi < argc &&
         !eq_cstr(argv[argi], ")") &&
         !eq_cstr(argv[argi], "]"))
  {
    const char* arg = argv[argi++];
    if (eq_cstr (arg, "-def")) {
      if (argi + 1 >= argc) {
        failout_sysCx("2 arguments needed for -def.\n");
      }
      const char* key = argv[argi++];
      const char* val = argv[argi++];
      uint x = 0;
      if (!xget_uint_cstr (&x, val))
        failout_sysCx("Argument Usage: -def KEY VAL\nWhere VAL is an unsigned integer!");
      psys_opt.constant_map[key] = x;
    }
    else if (handle_param_arg (psys_opt, arg, argi, argc, argv))
    {}
    else if (eq_cstr (arg, "-no-partial")) {
      psys_opt.partial = false;
    }
  }
  if (argi >= argc) {
    failout_sysCx("Need closing paren for -param!");
  }
  ++ argi;

  return true;
}

static
  bool
protocon_options_rec
  (int& argi,
   int argc,
   char** argv,
   AddConvergenceOpt& opt,
   ProtoconFileOpt& infile_opt,
   ProtoconOpt& exec_opt,
   ProblemInstance& problem)
{
  Cx::OFile of( stderr_OFile() );
  while (pfxeq_cstr ("-", argv[argi])) {
    const char* arg = argv[argi++];
    if (eq_cstr (arg, "-o-promela") ||
        eq_cstr (arg, "-o-model")) {
      if (!argv[argi]) {
        DBog1("No path given for %s!!!", arg);
        return false;
      }
      exec_opt.model_ofilepath = argv[argi++];
    }
    else if (eq_cstr (arg, "-o-graphviz")) {
      exec_opt.graphviz_ofilepath = argv[argi++];
    }
    else if (eq_cstr (arg, "-serial")) {
      exec_opt.nparallel = 1;
    }
    else if (eq_cstr (arg, "-parallel")) {
      exec_opt.nparallel = 0;
      if (argv[argi] && argv[argi][0] != '-') {
        arg = argv[argi++];
        if (!xget_uint_cstr (&exec_opt.nparallel, arg)) {
          failout_sysCx("Number given to -parallel could not be parsed.\n");
        }
      }
    }
    else if (eq_cstr (arg, "-search")) {
      opt.search_method = opt.BacktrackSearch;
    }
    else if (eq_cstr (arg, "-rank-shuffle")) {
      opt.search_method = opt.RankShuffleSearch;
    }
    else if (eq_cstr (arg, "-test")) {
      exec_opt.task = ProtoconOpt::TestTask;
    }
    else if (eq_cstr (arg, "-verify")) {
      exec_opt.task = ProtoconOpt::VerifyTask;
    }
    else if (eq_cstr (arg, "-minimize-conflicts")) {
      exec_opt.task = ProtoconOpt::MinimizeConflictsTask;
      exec_opt.conflict_order = ProtoconOpt::HiLoOrder;
    }
    else if (eq_cstr (arg, "-minimize-conflicts-hilo")) {
      exec_opt.task = ProtoconOpt::MinimizeConflictsTask;
      exec_opt.conflict_order = ProtoconOpt::HiLoOrder;
    }
    else if (eq_cstr (arg, "-minimize-conflicts-lohi")) {
      exec_opt.task = ProtoconOpt::MinimizeConflictsTask;
      exec_opt.conflict_order = ProtoconOpt::LoHiOrder;
    }
    else if (eq_cstr (arg, "-minimize-conflicts-random")) {
      exec_opt.task = ProtoconOpt::MinimizeConflictsTask;
      exec_opt.conflict_order = ProtoconOpt::RandomOrder;
    }
    else if (eq_cstr (arg, "-interactive")) {
      exec_opt.task = ProtoconOpt::InteractiveTask;
    }
    else if (eq_cstr (arg, "-nop")) {
      exec_opt.task = ProtoconOpt::NoTask;
    }
    else if (eq_cstr (arg, "-h") || eq_cstr (arg, "-help")) {
      DBog0( "See the manpage for details: man ./doc/protocon.1" );
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
      exec_opt.params[0].constant_map[key] = x;
    }
    else if (handle_param_arg (exec_opt.params[0], arg, argi, argc, argv))
    {}
    else if (eq_cstr (arg, "-param")) {
      if (!parse_param(exec_opt, argi, argc, argv)) {
        return false;
      }
    }
    else if (eq_cstr (arg, "-x")) {
      DBog0("Instance: From File");
      problem = FromFileInstance;
      arg = argv[argi++];
      if (!arg) {
        failout_sysCx("Not enuff arguments.");
      }
      if (eq_cstr (arg, "-list")) {
        while (argi < argc) {
          arg = argv[argi++];
          if (eq_cstr(arg, ".")) {
            break;
          }
          exec_opt.xfilepaths.push(arg);
          if (!infile_opt.file_path) {
            infile_opt.file_path = arg;
          }
        }
      }
      else {
        infile_opt.file_path = arg;
      }
    }
    else if (eq_cstr (arg, "-x-args")) {
      Cx::String args_xfilepath( argv[argi++] );
      if (!args_xfilepath) {
        of << "-x-args requires an argument!" << of.endl();
        return false;
      }
      Cx::C::XFileB args_xf;
      init_XFileB (&args_xf);
      if (!open_FileB (&args_xf.fb, 0, args_xfilepath.cstr())) {
        of << "-x-args could not be opened!" << of.endl();
        return false;
      }
      xget_XFileB (&args_xf);

      XFile olay;
      olay_txt_XFile (&olay, &args_xf.xf, 0);
      Cx::Table<char*> xargs;
      char* xarg;
      do {
        xarg = nextok_XFile (&olay, 0, WhiteSpaceChars);
        if (pfxeq_cstr("#", xarg)) {
          skiplined_XFile (&olay, "\n");
        }
        else {
          xargs.push(xarg);
        }
      } while (xarg);
      int tmp_argi = 0;
      int tmp_argc = xargs.sz()-1;
      if (!protocon_options_rec
          (tmp_argi, tmp_argc, &xargs[0], opt, infile_opt, exec_opt, problem))
      {
        return false;
      }
      lose_XFile (&olay);
      lose_XFileB (&args_xf);
    }
    else if (eq_cstr (arg, "-o")) {
      if (!argv[argi]) {
        failout_sysCx("Not enuff arguments.");
      }
      exec_opt.ofilepath = argv[argi++];
    }
    else if (eq_cstr (arg, "-espresso")) {
      exec_opt.use_espresso = true;
    }
    else if (eq_cstr (arg, "-x-test-known")) {
      Xn::Sys test_sys;
      ProtoconFileOpt file_opt;
      if (!argv[argi]) {
        failout_sysCx("Not enuff arguments for -x-test-known.");
      }
      file_opt.file_path = argv[argi++];
      if (!ReadProtoconFile(test_sys, file_opt)) {
        failout_sysCx("Reading -x-test-known file.");
      }
      opt.known_solution = test_sys.actions;
    }
    else if (eq_cstr (arg, "-o-log")) {
      exec_opt.log_ofilename = argv[argi++];
      if (!exec_opt.log_ofilename) {
        of << "-o-log requires an argument!" << of.endl();
        return false;
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
    else if (eq_cstr (arg, "-optimize")) {
      opt.optimize_soln = true;
    }
    else if (eq_cstr (arg, "-solution-as-conflict")) {
      opt.solution_as_conflict = true;
    }
    else if (eq_cstr (arg, "-o-livelock")) {
      if (!argv[argi]) {
        failout_sysCx("Not enuff arguments.");
      }
      opt.livelock_ofilepath = argv[argi++];
    }
    else if (eq_cstr (arg, "-x-conflicts")) {
      exec_opt.conflicts_xfilepath = argv[argi++];
      if (!exec_opt.conflicts_xfilepath) {
        of << "-x-conflicts requires an argument!" << of.endl();
        return false;
      }
    }
    else if (eq_cstr (arg, "-o-conflicts")) {
      exec_opt.conflicts_ofilepath = argv[argi++];
      if (!exec_opt.conflicts_ofilepath) {
        of << "-o-conflicts requires an argument!" << of.endl();
        return false;
      }
    }
    else if (eq_cstr (arg, "-snapshot-conflicts")) {
      opt.snapshot_conflicts = true;
    }
    else if (eq_cstr (arg, "-max-conflict")) {
      if (!xget_uint_cstr (&opt.max_conflict_sz, argv[argi++])) {
        failout_sysCx("Argument Usage: -max-conflict N");
      }
    }
    else if (eq_cstr (arg, "-no-random")) {
      opt.randomize_pick = false;
    }
    else if (eq_cstr (arg, "-sysrand")) {
      opt.system_urandom = true;
    }
    else if (eq_cstr (arg, "-")) {
      opt.randomize_pick = false;
    }
    else if (eq_cstr (arg, "-max-depth")) {
      if (!xget_uint_cstr (&opt.max_depth, argv[argi++])) {
        failout_sysCx("Argument Usage: -max-depth N");
      }
    }
    else if (eq_cstr (arg, "-max-height")) {
      if (!xget_uint_cstr (&opt.max_height, argv[argi++])) {
        failout_sysCx("Argument Usage: -max-height N");
      }
    }
    else if (eq_cstr (arg, "-pick-reach")) {
      opt.pick_back_reach = true;
    }
    else if (eq_cstr (arg, "-pick")) {
      const char* method = argv[argi++];
      if (eq_cstr (method, "mcv")) {
        opt.pick_method = opt.MCVLitePick;
      }
      else if (eq_cstr (method, "greedy")) {
        opt.pick_method = opt.GreedyPick;
      }
      else if (eq_cstr (method, "lcv")) {
        opt.pick_method = opt.LCVLitePick;
      }
      else if (eq_cstr (method, "fully-random")) {
        opt.pick_method = opt.FullyRandomPick;
      }
      else if (eq_cstr (method, "conflict")) {
        opt.pick_method = opt.ConflictPick;
      }
      else if (eq_cstr (method, "quick")) {
        opt.pick_method = opt.QuickPick;
      }
      else {
        failout_sysCx("Argument Usage: -pick [mcv|greedy|lcv|quick]");
      }
    }
    else {
      failout_sysCx(arg);
    }
  }
  return true;
}


  bool
protocon_options
  (Xn::Sys& sys,
   int argi,
   int argc,
   char** argv,
   AddConvergenceOpt& opt,
   ProtoconFileOpt& infile_opt,
   ProtoconOpt& exec_opt)
{
  ProblemInstance problem = NProblemInstances;
  uint npcs = 4;
  if (!protocon_options_rec (argi, argc, argv, opt, infile_opt, exec_opt, problem))
    return false;

  if (exec_opt.task == ProtoconOpt::TestTask)
    return true;

  if (problem == FromFileInstance) {
  }
  else if (argi < argc) {
    if (false) {
    }
    else if (string(argv[argi]) == "3-coloring") {
      DBog0("Instance: 3-Coloring on Bidirectional Ring");
      problem = ThreeColoringRingInstance;
    }
    else if (string(argv[argi]) == "2-coloring") {
      DBog0("Instance: 2-Coloring on Unidirectional Ring");
      problem = TwoColoringRingInstance;
    }
    else if (string(argv[argi]) == "matching") {
      DBog0("Instance: Maximal Matching");
      problem = MaximalMatchingInstance;
    }
    else if (string(argv[argi]) == "sum-not-2") {
      DBog0("Instance: Sum-Not-2");
      problem = SumNotTwoInstance;
    }
    else if (string(argv[argi]) == "agreement") {
      DBog0("Instance: Agreement");
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

  infile_opt.constant_map = exec_opt.params[0].constant_map;

  if (exec_opt.xfilepaths.sz() == 0) {
    if (!!infile_opt.file_path) {
      exec_opt.xfilepaths.push(infile_opt.file_path);
    }
  }

  // Set up the chosen problem.
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
      return false;
  }

  if (!sys.integrityCk()) {
    failout_sysCx ("Bad system definition.");
  }
  return true;
}

