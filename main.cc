
extern "C" {
#include "cx/syscx.h"
}

#include "stability.hh"
#include "pla.hh"
#include "cx/fileb.hh"


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
               StabilitySynLvl& tape,
               const AddConvergenceOpt& opt)
{
  while (!tape.candidates.empty()) {
    if (!sys.shadow_puppet_synthesis_ck()) {
      if (!WeakConvergenceCk(sys, tape.hiXnRel, sys.invariant)) {
        return false;
      }
    }
    else {
      if (!WeakConvergenceCk(sys, tape.hiXnRel, tape.hi_invariant)) {
        return false;
      }
    }

    // Pick the action.
    uint actId = 0;
    if (!PickActionMCV(actId, sys, tape, opt)) {
      return false;
    }

    StabilitySynLvl next( tape );
    next.bt_dbog = (tape.bt_dbog && (true || tape.bt_level < 18));
    next.bt_level = tape.bt_level + 1;
    next.reviseActions(sys, Set<uint>(actId), Set<uint>());

    bool found = AddConvergence(retActions, sys, next, opt);
    if (found) {
      return true;
    }
    tape.reviseActions(sys, Set<uint>(), Set<uint>(actId));
  }

  if (tape.deadlockPF.tautology_ck(false)) {
    const PF& invariant = sys.shadow_puppet_synthesis_ck() ? tape.hi_invariant : sys.invariant;
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
    retActions = tape.actions;
    return true;
  }
  return false;
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
  Xn::Net& topo = sys.topology;

  StabilitySynLvl tape;
  tape.loXnRel = false;
  tape.hiXnRel = false;

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

  {
    const bool forcePrune = true;
    tape.bt_dbog = true;
    tape.reviseActions(sys, Set<uint>(sys.actions), Set<uint>(), forcePrune);
  }

  if (tape.deadlockPF.tautology_ck(false) &&
      tape.actions.size() == sys.actions.size() &&
      tape.candidates.size() == 0)
  {
    DBog0("The given protocol is self-stabilizing.");
  }

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
  const char* infile_path = 0;
  const char* outfile_path = 0;
  bool use_random_method = false;

  // Use to disable picking only actions which resolve deadlocks
  // by making them backwards reachable from the invariant.
  //opt.pickBackReach = false;
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
      use_random_method = true;
    }
    else if (eq_cstr (arg, "-test")) {
      DBog0( "Running tests..." );
      Test();
      DBog0( "Done." );
      lose_sysCx ();
      return 0;
    }
    else if (eq_cstr (arg, "-x")) {
      DBog0("Problem: From File");
      problem = FromFileInstance;
      infile_path = argv[argi++];
      if (!infile_path) {
        failout_sysCx("Not enuff arguments.\n");
      }
    }
    else if (eq_cstr (arg, "-o")) {
      outfile_path = argv[argi++];
      if (!outfile_path) {
        failout_sysCx("Not enuff arguments.\n");
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
      if (!ReadProtoconFile(sys, infile_path))
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
  // Run the algorithm.
  if (use_random_method) {
    if (!infile_path) {
      failout_sysCx ("Need to use input file with random method!");
    }
    found = ordering_synthesis(sys.actions, infile_path);
  }
  else {
    found = AddConvergence(sys, opt);
  }

  if (found) {
    DBog0("Solution found!");
    for (uint i = 0; i < sys.actions.size(); ++i) {
      const Xn::Net& topo = sys.topology;
      Xn::ActSymm act;
      topo.action(act, sys.actions[i]);
      OPut(DBogOF, act) << '\n';
    }
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
  else {
    DBog0("No solution found...");
  }
  std::flush(DBogOF);

  lose_sysCx ();
  return 0;
}

