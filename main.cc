
extern "C" {
#include "cx/syscx.h"
}

#include "stabilization.hh"
#include "synthesis.hh"
#include "pla.hh"
#include "cx/fileb.hh"
#include "search.hh"

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
  ProtoconOpt exec_opt;

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
  if (exec_opt.task == ProtoconOpt::VerifyTask) {
    found = stabilization_ck(DBogOF, sys);
  }
  else if (exec_opt.task == ProtoconOpt::MinimizeConflictsTask) {
    if (!infile_opt.file_path) {
      failout_sysCx ("Need to use input file with random or -minimize-conflicts method!");
    }
    stabilization_search(sys.actions, infile_opt, exec_opt, opt);
  }
  else if (opt.search_method != opt.BacktrackSearch) {
    if (!infile_opt.file_path) {
      failout_sysCx ("Need to use input file with random or rank/shuffle method!");
    }
    found =
      stabilization_search(sys.actions, infile_opt, exec_opt, opt);
  }
  else {
    found = AddConvergence(sys, opt);
  }

  if (exec_opt.task == ProtoconOpt::VerifyTask) {
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

