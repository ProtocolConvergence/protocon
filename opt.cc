
extern "C" {
#include "cx/syscx.h"
}

#include "opt.hh"
#include "stabilization.hh"
#include "synthesis.hh"
#include "pla.hh"
#include "cx/fileb.hh"
#include "search.hh"

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
    else if (eq_cstr (arg, "-no-conflict")) {
      psys_opt.conflict = false;
    }
    else if (eq_cstr (arg, "-no-conflicts")) {
      psys_opt.conflict = false;
    }
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


  bool
protocon_options
  (Xn::Sys& sys,
   int argi,
   int argc,
   char** argv,
   AddConvergenceOpt& opt,
   const char*& modelFilePath,
   ProtoconFileOpt& infile_opt,
   ProtoconOpt& exec_opt)
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
  uint npcs = 4;
  while (pfxeq_cstr ("-", argv[argi])) {
    const char* arg = argv[argi++];
    if (eq_cstr (arg, "-o-model")) {
      modelFilePath = argv[argi++];
      if (!modelFilePath){
        DBog0("No path given!!!!");
      }
    }
    else if (eq_cstr (arg, "-simple")) {
      opt.search_method = opt.SimpleBacktrackSearch;
    }
    else if (eq_cstr (arg, "-random")) {
      opt.search_method = opt.RandomBacktrackSearch;
    }
    else if (eq_cstr (arg, "-rank-shuffle")) {
      opt.search_method = opt.RankShuffleSearch;
    }
    else if (eq_cstr (arg, "-test")) {
      exec_opt.task = ProtoconOpt::TestTask;
      return true;
    }
    else if (eq_cstr (arg, "-verify")) {
      exec_opt.task = ProtoconOpt::VerifyTask;
    }
    else if (eq_cstr (arg, "-minimize-conflicts")) {
      exec_opt.task = ProtoconOpt::MinimizeConflictsTask;
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
    else if (eq_cstr (arg, "-no-conflict")) {
      exec_opt.params[0].conflict = false;
    }
    else if (eq_cstr (arg, "-no-conflicts")) {
      exec_opt.params[0].conflict = false;
    }
    else if (eq_cstr (arg, "-param")) {
      if (!parse_param(exec_opt, argi, argc, argv)) {
        return false;
      }
    }
    else if (eq_cstr (arg, "-x")) {
      DBog0("Problem: From File");
      problem = FromFileInstance;
      infile_opt.file_path = argv[argi++];
      if (!infile_opt.file_path) {
        failout_sysCx("Not enuff arguments.");
      }
    }
    else if (eq_cstr (arg, "-o")) {
      if (!argv[argi]) {
        failout_sysCx("Not enuff arguments.");
      }
      exec_opt.ofilepath = argv[argi++];
    }
    else if (eq_cstr (arg, "-x-test-known")) {
      Xn::Sys test_sys;
      ProtoconFileOpt file_opt;
      file_opt.file_path = argv[argi++];
      if (!file_opt.file_path) {
        failout_sysCx("Not enuff arguments for -x-test-known.");
      }
      if (!ReadProtoconFile(test_sys, file_opt)) {
        failout_sysCx("Reading -x-test-known file.");
      }
      opt.known_solution = test_sys.actions;
    }
    else if (eq_cstr (arg, "-o-log")) {
      exec_opt.log_ofilename = argv[argi++];
      if (!exec_opt.log_ofilename) {
        failout_sysCx("Argument Usage: -o-log FILE");
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
        opt.pick_method = opt.RandomPick;
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

  infile_opt.constant_map = exec_opt.params[0].constant_map;

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

