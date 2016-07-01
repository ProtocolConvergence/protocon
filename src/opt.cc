
extern "C" {
#include "cx/syscx.h"
}

#include "opt.hh"
#include "synthesis.hh"
#include "prot-ofile.hh"
#include "cx/fileb.hh"
#include "search.hh"

#ifndef _WIN32
#include <sys/resource.h>
#endif

#include "namespace.hh"

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
  void
ReadFileText (String& ret_text, const char* filename)
{
  const bool use_stdin = eq_cstr ("-", filename);
  AlphaTab text = textfile_AlphaTab (0, use_stdin ? 0 : filename);
  if (text.sz == 0) {
    if (use_stdin) {
      failout_sysCx ("Could not read standard input.");
    }
    else {
      String msg( "Could not read file: " );
      msg += filename;
      failout_sysCx (msg.cstr());
    }
  }
  ret_text = text;
  lose_AlphaTab( &text );
}

static
  bool
eqck_skipws (const char* a, const char* b)
{
  uint i = 0;
  uint j = 0;
  if (!a)  a = "";
  if (!b)  b = "";
  while (true) {
    if (a[i]==' ') {
      ++i;
    }
    else if (b[j]==' ') {
      ++j;
    }
    else if (a[i]!=b[j]) {
      return false;
    }
    else if (a[i]=='\0') {
      return true;
    }
    else {
      ++i;
      ++j;
    }
  }
  return false;
}

static
  bool
parse_style (ProtoconFileOpt& opt, const char* arg)
{
#define M(str)  (eqck_skipws(arg, str))
  /* */if M("(future & closed)") {
    opt.invariant_style = Xn::FutureAndClosed;
    opt.invariant_scope = Xn::DirectInvariant;
  }
  else if M("(future & silent)") {
    opt.invariant_style = Xn::FutureAndSilent;
    opt.invariant_scope = Xn::DirectInvariant;
  }
  else if M("(future & shadow)") {
    opt.invariant_style = Xn::FutureAndShadow;
    opt.invariant_scope = Xn::DirectInvariant;
  }
  else if M("(future & active shadow)") {
    opt.invariant_style = Xn::FutureAndActiveShadow;
    opt.invariant_scope = Xn::DirectInvariant;
  }
  else if M("((future & closed) % puppet)") {
    opt.invariant_style = Xn::FutureAndClosed;
    opt.invariant_scope = Xn::ShadowInvariant;
  }
  else if M("((future & silent) % puppet)") {
    opt.invariant_style = Xn::FutureAndSilent;
    opt.invariant_scope = Xn::ShadowInvariant;
  }
  else if M("((future & shadow) % puppet)") {
    opt.invariant_style = Xn::FutureAndShadow;
    opt.invariant_scope = Xn::ShadowInvariant;
  }
  else if M("(future & silent)") {
    opt.invariant_style = Xn::FutureAndShadow;
    opt.invariant_scope = Xn::FutureInvariant;
  }
  else if M("(future & future shadow)") {
    opt.invariant_style = Xn::FutureAndShadow;
    opt.invariant_scope = Xn::FutureInvariant;
  }
  else if M("future silent") {
    opt.invariant_behav = Xn::FutureSilent;
  }
  else if M("future shadow") {
    opt.invariant_behav = Xn::FutureShadow;
  }
  else if M("future active shadow") {
    opt.invariant_behav = Xn::FutureActiveShadow;
  }
  else {
    return false;
  }
  return true;
#undef M
}

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
  else if (eq_cstr (arg, "-uniring")) {
    psys_opt.stabilization_opt.uniring = true;
  }
  else if (eq_cstr (arg, "-count-convergence-layers")) {
    psys_opt.stabilization_opt.count_convergence_layers = true;
  }
  else if (eq_cstr (arg, "-count-convergence-steps")) {
    psys_opt.stabilization_opt.count_convergence_layers = true;
    psys_opt.stabilization_opt.count_convergence_steps = true;
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
parse_NatMap (Xn::NatMap& tup, const char* line)
{
  DeclLegit( good );
  tup = Xn::NatMap();
  ::XFile xf[1];
  init_XFile_olay_cstr (xf, (char*)line);
  if (line[0] == '(') {
    tup.scalar = false;
  }
  skipds_XFile (xf, "(");
  int x = 0;

  if (strstr(line, "..")) {
    int begval = 0;
    int endval = 0;

    DoLegitLine("")
      xget_int_XFile (xf, &begval);
    skipds_XFile (xf, 0);
    skipds_XFile (xf, ".");
    DoLegitLine("")
      xget_int_XFile (xf, &endval);

    DoLegit("") {
      int diff = (begval < endval ? 1 : -1);
      for (int val = begval; val != endval + diff; val += diff) {
        tup.membs << val;
      }
    }
  }
  else {
    while (xget_int_XFile (xf, &x)) {
      tup.membs << x;
      skipds_XFile (xf, 0);
      skipds_XFile (xf, ",)");
    }

    good = (tup.membs.sz() > 0 || line[0]=='(');
  }

  DoLegit( "" ) {
    if (tup.membs.sz() == 1) {
      tup.expression << tup.membs[0];
    }
    else {
      tup.expression << '(';
      for (uint i = 0; i < tup.membs.sz(); ++i) {
        if (i > 0)
          tup.expression << ",";
        tup.expression << tup.membs[i];
      }
      tup.expression << ')';
    }
  }
  return !!good;
}

static
  void
push_instances(Table< ProtoconParamOpt >& instances,
               const ProtoconParamOpt& instdef)
{
  const uint begidx = instances.sz();

  {
    ProtoconParamOpt& instance = instances.grow1();
    instance = instdef;
    Map<String, Xn::NatMap>::iterator param_it = instance.constant_map.begin();
    while (param_it != instance.constant_map.end()) {
      Xn::NatMap& tup = param_it->second;
      if (tup.scalar) {
        tup.membs.resize(1);
      }
      ++ param_it;
    }
  }

  Map<String, Xn::NatMap>::const_iterator param_it = instdef.constant_map.begin();
  while (param_it != instdef.constant_map.end()) {
    const String& key = param_it->first;
    const Xn::NatMap& param_range = param_it->second;
    const uint endidx = instances.sz();
    if (param_range.scalar) {
      for (uint i = 1; i < param_range.sz(); ++i) {
        for (uint j = begidx; j < endidx; ++j) {
          ProtoconParamOpt& instance = instances.grow1();
          instance = instances[j];
          instance.constant_map[key] = param_range.eval(i);
        }
      }
    }
    ++ param_it;
  }
}

static
  bool
parse_param(ProtoconOpt& opt, int& argi, int argc, char** argv)
{
  static const char SyntaxMsg[] =
    "Argument Usage: -param KEY VAL\nWhere VAL is an integer, list, or range!";

  ProtoconParamOpt instdef = opt.instance_def;

  if (!eq_cstr(argv[argi], "(") &&
      !eq_cstr(argv[argi], "[")) {
    if (argi + 1 >= argc) {
      failout_sysCx("2 arguments needed for -param.\n");
    }
    const char* key = argv[argi++];
    const char* val = argv[argi++];

    if (!parse_NatMap (instdef.constant_map[key], val))
      failout_sysCx(SyntaxMsg);
    push_instances(opt.instances, instdef);
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
      if (!parse_NatMap (instdef.constant_map[key], val))
        failout_sysCx(SyntaxMsg);
    }
    else if (handle_param_arg (instdef, arg, argi, argc, argv))
    {}
    else if (eq_cstr (arg, "-no-partial")) {
      instdef.partial = false;
    }
  }
  if (argi >= argc) {
    failout_sysCx("Need closing paren for -param!");
  }
  ++ argi;
  push_instances(opt.instances, instdef);

  return true;
}

static
  bool
protocon_options_rec
  (int& argi,
   int argc,
   char** argv,
   const char* relpath,
   AddConvergenceOpt& opt,
   ProtoconFileOpt& infile_opt,
   ProtoconOpt& exec_opt,
   ProblemInstance& problem)
{
  OFile of( stderr_OFile() );
  while (pfxeq_cstr ("-", argv[argi])) {
    ::AlphaTab tmpf = dflt_AlphaTab ();
    const int prev_argi = argi;
    bool copy_to_argline = true;

    const char* arg = argv[argi++];
    if (eq_cstr (arg, "-o-promela") ||
        eq_cstr (arg, "-o-pml")) {
      if (!argv[argi]) {
        DBog1("No path given for %s!!!", arg);
        return false;
      }
      exec_opt.model_ofilepath = argv[argi++];
    }
    else if (eq_cstr (arg, "-o-graphviz")) {
      exec_opt.graphviz_ofilepath = argv[argi++];
    }
    else if (eq_cstr (arg, "-o-udp")) {
      exec_opt.udp_ofilepath = argv[argi++];
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
      if (!parse_NatMap (exec_opt.instance_def.constant_map[key], val))
        failout_sysCx("Argument Usage: -def KEY VAL\nWhere VAL is an integer, list, or range!");
    }
    else if (handle_param_arg (exec_opt.instance_def, arg, argi, argc, argv))
    {}
    else if (eq_cstr (arg, "-param")) {
      if (!parse_param(exec_opt, argi, argc, argv)) {
        return false;
      }
    }
    else if (eq_cstr (arg, "-x")) {
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
          pathname2_AlphaTab (&tmpf, relpath, arg);
          exec_opt.xfilepaths.push(String(tmpf));
          if (!exec_opt.xfilepath) {
            exec_opt.xfilepath = tmpf;
          }
        }
      }
      else {
        pathname2_AlphaTab (&tmpf, relpath, arg);
        exec_opt.xfilepath = tmpf;
      }
      infile_opt.constant_map = exec_opt.instance_def.constant_map;
    }
    else if (eq_cstr (arg, "-x-args")) {
      copy_to_argline = false;
      String args_xfilepath( argv[argi++] );
      if (!args_xfilepath) {
        of << "-x-args requires an argument!" << of.endl();
        return false;
      }
      ::XFileB args_xf;
      init_XFileB (&args_xf);
      if (!open_FileB (&args_xf.fb, relpath, args_xfilepath.cstr())) {
        of << "Could not open -x-args file: " << args_xfilepath.cstr() << of.endl();
        return false;
      }
      xget_XFileB (&args_xf);

      ::XFile olay;
      olay_txt_XFile (&olay, &args_xf.xf, 0);
      Table<char*> xargs;
      char* xarg;
      do {
        char matched_delim = '\0';
        xarg = nextok_XFile (&olay, &matched_delim, WhiteSpaceChars);
        if (pfxeq_cstr("#", xarg)) {
          if (matched_delim != '\n') {
            skiplined_XFile (&olay, "\n");
          }
        }
        else if (pfxeq_cstr("'", xarg)) {
          putlast_char_XFile (&olay, matched_delim);
          offto_XFile (&olay, xarg);
          xarg = nextok_XFile (&olay, 0, "'");
          xargs.push(xarg);
        }
        else if (pfxeq_cstr("\"", xarg)) {
          putlast_char_XFile (&olay, matched_delim);
          offto_XFile (&olay, xarg);
          xarg = nextok_XFile (&olay, 0, "\"");
          xargs.push(xarg);
        }
        else {
          xargs.push(xarg);
        }
      } while (xarg);
      int tmp_argi = 0;
      int tmp_argc = xargs.sz()-1;
      if (!protocon_options_rec
          (tmp_argi, tmp_argc, &xargs[0],
           ccstr_of_AlphaTab (&args_xf.fb.pathname),
           opt, infile_opt, exec_opt, problem))
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

      pathname2_AlphaTab (&tmpf, relpath, argv[argi++]);
      exec_opt.ofilepath = tmpf;
    }
    else if (eq_cstr (arg, "-espresso")) {
      exec_opt.use_espresso = true;
    }
    else if (eq_cstr (arg, "-x-test-known")) {
      Xn::Sys test_sys;
      ProtoconFileOpt file_opt;
      file_opt.constant_map = exec_opt.instance_def.constant_map;
      const char* const filename = argv[argi++];
      if (!filename) {
        failout_sysCx("Not enuff arguments for -x-test-known.");
      }
      pathname2_AlphaTab (&tmpf, relpath, filename);
      ReadFileText (file_opt.text, ccstr_of_AlphaTab (&tmpf));
      if (!ReadProtoconFile(test_sys, file_opt)) {
        failout_sysCx("Reading -x-test-known file.");
      }
      opt.known_solution = test_sys.actions;
    }
    else if (eq_cstr (arg, "-x-try") ||
             eq_cstr (arg, "-x-try-subset")) {
      Xn::Sys try_sys;
      ProtoconFileOpt file_opt;
      file_opt.constant_map = exec_opt.instance_def.constant_map;
      const char* const filename = argv[argi++];
      if (!filename) {
        failout_sysCx("Not enuff arguments for -x-try.");
      }

      pathname2_AlphaTab (&tmpf, relpath, filename);
      ReadFileText (file_opt.text, ccstr_of_AlphaTab (&tmpf));
      if (!ReadProtoconFile(try_sys, file_opt)) {
        failout_sysCx("Reading -x-try file.");
      }
      if (eq_cstr (arg, "-x-try-subset")) {
        opt.subset_solution_guesses |= opt.solution_guesses.sz();
      }
      opt.solution_guesses.push(try_sys.actions);
    }
    else if (eq_cstr (arg, "-o-log")) {
      if (!argv[argi]) {
        of << "-o-log requires an argument!" << of.endl();
        return false;
      }
      pathname2_AlphaTab (&tmpf, relpath, argv[argi++]);
      exec_opt.log_ofilename = tmpf;
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
    else if (eq_cstr (arg, "-o-stats")) {
      exec_opt.stats_ofilepath = argv[argi++];
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
    else if (eq_cstr (arg, "-randomize-depth")) {
      if (!xget_uint_cstr (&opt.randomize_depth, argv[argi++])) {
        failout_sysCx("Argument Usage: -randomize-depth N");
      }
    }
    else if (eq_cstr (arg, "-sysrand")) {
      opt.system_urandom = true;
    }
#ifndef _WIN32
    else if (eq_cstr (arg, "-peak-MB")) {
      // This limits virtual memory, which could be
      // twice the amount that is actually used (i.e., resident)!
      luint megabytes = 0;
      struct rlimit rlim;
      if (!xget_luint_cstr (&megabytes, argv[argi++])) {
        failout_sysCx("Argument Usage: -peak-MB NUMBER");
      }
      rlim.rlim_max = megabytes * 1000 * 1000;
      rlim.rlim_cur = rlim.rlim_max;
      setrlimit(RLIMIT_AS, &rlim);
      rlim.rlim_max = 0;
      rlim.rlim_cur = 0;
      setrlimit(RLIMIT_CORE, &rlim);
    }
#endif
    else if (eq_cstr (arg, "-disabling")) {
      opt.force_disabling = true;
    }
    else if (eq_cstr (arg, "-pure")) {
      opt.pure_actions = true;
    }
    else if (eq_cstr (arg, "-prep-conflicts")) {
      opt.prep_conflicts = true;
    }
    else if (eq_cstr (arg, "-fast-deadlock-mrv")) {
      opt.fast_deadlock_mrv = true;
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
      if (eq_cstr (method, "mrv")) {
        opt.pick_method = opt.MRVLitePick;
      }
      else if (eq_cstr (method, "lex")) {
        opt.pick_method = opt.LexPick;
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
        failout_sysCx("Argument Usage: -pick [mrv|greedy|lcv|quick]");
      }
    }
    else if (eq_cstr (arg, "-style")) {
      arg = argv[argi++];
      if (!parse_style (infile_opt, arg)) {
        failout_sysCx("Bad -style");
      }
    }
    else {
      failout_sysCx(arg);
    }
    if (copy_to_argline) {
      for (int i = prev_argi; i < argi; ++i) {
        exec_opt.argline << " " << argv[i];
      }
    }
    lose_AlphaTab (&tmpf);
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
  exec_opt.argline = exename_of_sysCx ();
  uint npcs = 4;
  if (!protocon_options_rec (argi, argc, argv, 0,
                             opt, infile_opt, exec_opt, problem))
    return false;

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

  if (exec_opt.xfilepaths.sz() == 0) {
    if (!!exec_opt.xfilepath) {
      exec_opt.xfilepaths.push(exec_opt.xfilepath);
    }
  }

  if (exec_opt.instances.sz() == 0) {
    push_instances(exec_opt.instances, exec_opt.instance_def);
  }

  // Set up the chosen problem.
  switch(problem){
    case FromFileInstance:
      ReadFileText (infile_opt.text, exec_opt.xfilepath.cstr());
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

END_NAMESPACE

