
extern "C" {
#include "cx/syscx.h"
}

#include "opt.hh"
#include "stabilization.hh"
#include "synthesis.hh"
#include "pla.hh"
#include "cx/fileb.hh"
#include "search.hh"

  bool
protocon_options
  (Xn::Sys& sys,
   int argi,
   int argc,
   char** argv,
   AddConvergenceOpt& opt,
   const char*& modelFilePath,
   ProtoconFileOpt& infile_opt,
   const char*& outfile_path,
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
      exec_opt.task = ProtoconOpt::TestTask;
      return true;
    }
    else if (eq_cstr (arg, "-verify")) {
      exec_opt.task = ProtoconOpt::VerifyTask;
    }
    else if (eq_cstr (arg, "-minimize-conflicts")) {
      exec_opt.task = ProtoconOpt::MinimizeConflictsTask;
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
    else if (eq_cstr (arg, "-param")) {
      if (argi + 1 >= argc) {
        failout_sysCx("2 arguments needed for -param.\n");
      }
      const char* key = argv[argi++];
      const char* val = argv[argi++];
      uint x = 0;
      if (!xget_uint_cstr (&x, val))
        failout_sysCx("Argument Usage: -param KEY VAL\nWhere VAL is an unsigned integer!");
      exec_opt.params.push(std::make_pair<Cx::String,uint>(key, x));
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
      else if (eq_cstr (method, "quick")) {
        opt.pick_method = opt.QuickPick;
      }
      else if (eq_cstr (method, "random")) {
        opt.pick_method = opt.RandomPick;
      }
      else if (eq_cstr (method, "conflict")) {
        opt.pick_method = opt.ConflictPick;
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

