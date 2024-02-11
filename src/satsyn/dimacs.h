
#include <fildesh/fildesh_compat_fd.h>
#include <fildesh/fildesh_compat_sh.h>

  void
oput_dimacs_CnfFmla(FildeshO* out, const CnfFmla* fmla)
{
  CnfDisj clause[] = {DEFAULT_CnfDisj};
  putstrlit_FildeshO(out, "p cnf ");
  print_int_FildeshO(out, (int)fmla->nvbls);
  putc_FildeshO(out, ' ');
  print_int_FildeshO(out, (int)fmla->idcs.sz);
  putc_FildeshO(out, '\n');
  for (unsigned i = 0; i < fmla->idcs.sz; ++i) {
    clause_of_CnfFmla (clause, fmla, i);
    for (unsigned j = 0; j < clause->lits.sz; ++j) {
      if (!clause->lits.s[j].val)
        putc_FildeshO(out, '-');
      print_int_FildeshO(out, (int)(1+clause->lits.s[j].vbl));
      putc_FildeshO(out, ' ');
    }
    putstrlit_FildeshO(out, "0\n");
  }
  lose_CnfDisj(clause);
}

  void
xget_dimacs_result (FildeshX* in, bool* sat, BitTable evs)
{
  FildeshX slice = sliceline_FildeshX(in);
  wipe_BitTable (evs, 0);
  if (!slice.at) {
    *sat = false;
    DBog0( "No output!" );
    return;
  }
  if (peek_bytestring_FildeshX(&slice, fildesh_bytestrlit("UNSAT")) ||
      peek_bytestring_FildeshX(&slice, fildesh_bytestrlit("unsat"))) {
    *sat = false;
  }
  else {
    int v = -1;
    bool good;
    *sat = true;

    good = parse_int_FildeshX(in, &v);
    while (good) {
      if      (v > 0)  set1_BitTable (evs, +v-1);
      else if (v < 0)  set0_BitTable (evs, -v-1);
      good = parse_int_FildeshX(in, &v);
    }
  }
}

/**
 * Use an external SAT solver to solve /fmla/.
 * If /\ref SatSolve_Z3==true/, use Z3.
 * Otherwise, use MiniSat.
 *
 * \param fmla  CNF formula to solve. This is freed before the solver is run!
 * \param sat   Result. Whether formula is satisfiable.
 * \param evs   Result. Satisfying valuation. This should be allocated to the
 * proper size!
 **/
  void
extl_solve_CnfFmla (CnfFmla* fmla, bool* sat, BitTable evs)
{
  const char* const z3_argv[] = {"z3", "-dimacs", "sat.in", NULL};
  const char* const minisat_argv[] = {"minisat", "-verb=0", "sat.in", "sat.out", NULL};
  const char* const* argv = (SatSolve_Z3 ? z3_argv : minisat_argv);
  Fildesh_fd out_solver_fd = -1;
  Fildesh_fd from_solver_fd = -1;
  int istat = 0;
  FildeshCompat_pid pid = -1;
  if (istat != 0) {
    fildesh_log_error("Failed to create pipe for solver.");
  }

  *sat = false;

  {
    FildeshO* out = open_FildeshOF("sat.in");
    oput_dimacs_CnfFmla(out, fmla);
    close_FildeshO(out);
  }

  lose_CnfFmla (fmla);
  *fmla = dflt_CnfFmla ();

  if (istat != 0) {
  }
  else if (SatSolve_Z3) {
    istat = fildesh_compat_fd_pipe(&out_solver_fd, &from_solver_fd);
    if (istat != 0) {
      fildesh_log_error("Failed to create pipe for solver.");
    }
  }

  if (istat != 0) {
    if (out_solver_fd >= 0) {
      fildesh_compat_fd_close(out_solver_fd);
    }
  }
  else {
    pid = fildesh_compat_fd_spawnvp(
        -1, out_solver_fd, 2, NULL, argv);
    if (pid < 0) {
      istat = -1;
      fildesh_log_errorf("Failed to spawn %s.", argv[0]);
    }
  }

  if (istat != 0) {
    if (from_solver_fd >= 0) {
      fildesh_compat_fd_close(from_solver_fd);
    }
  }
  else {
    FildeshX* in = NULL;
    if (SatSolve_Z3) {
      in = open_fd_FildeshX(from_solver_fd);
      xget_dimacs_result(in, sat, evs);
      fildesh_compat_sh_wait(pid);
    }
    else {
      fildesh_compat_sh_wait(pid);
      in = open_FildeshXF("sat.out");
      xget_dimacs_result(in, sat, evs);
    }
    close_FildeshX(in);
  }
}

