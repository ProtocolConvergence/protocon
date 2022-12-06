#include "src/satsyn/instance.h"
#include "src/satsyn/encodesat.h"
#include "src/satsyn/synsearch.h"
/* #include "fildesh/fildesh.h" */
#include <assert.h>
#include <iostream>

static
  void
write_dimacs_CnfFmla(std::ostream& out, const CnfFmla* fmla)
{
  CnfDisj clause[] = {DEFAULT_CnfDisj};
  out << "p cnf "
    << (unsigned) fmla->nvbls
    << ' '
    << (unsigned) fmla->idcs.sz
    << "\n";
  for (unsigned i = 0; i < fmla->idcs.sz; ++i) {
    clause_of_CnfFmla(clause, fmla, i);
    for (unsigned j = 0; j < clause->lits.sz; ++j) {
      if (!clause->lits.s[j].val) {
        out << '-';
      }
      out << (unsigned) (1+clause->lits.s[j].vbl);
      out << ' ';
    }
    out << "0\n";
  }
  lose_CnfDisj(clause);
}

static
  void
assert_expectations(const CnfFmla* fmla)
{
  CnfDisj clause[] = {DEFAULT_CnfDisj};
  BoolLit lit;
  assert(fmla->nvbls == 16);
  assert(fmla->idcs.sz == 22);

  clause_of_CnfFmla(clause, fmla, 0);
  assert(clause->lits.sz == 2);
  lit = clause->lits.s[0];
  assert(lit.vbl == 0 && !lit.val);
  lit = clause->lits.s[1];
  assert(lit.vbl == 8 && lit.val);

  lose_CnfDisj(clause);
}

int main()
{
  XnSys sys = inst_coloring_XnSys(2, 2);
  FMem_synsearch tape = cons1_FMem_synsearch(&sys);
  CnfFmla fmla = encode_sat(&tape);
  assert(fmla.nvbls > 0);

  write_dimacs_CnfFmla(std::cout, &fmla);
  assert_expectations(&fmla);

  lose_CnfFmla(&fmla);
  lose_FMem_synsearch(&tape);
  lose_XnSys(&sys);
  return 0;
}

