
#include "pf.hh"

#include <stdio.h>
#include "synhax.hh"

#define NPs 6

  void
init_unchanged(vector<PF>& unchange, PFCtx& ctx)
{
  unchange.resize(NPs);

  for (uint i = 0; i < NPs; ++i) {
    PF eq = (ctx.vbl(2*i+0) == ctx.vbl(2*i+1));

    for (uint j = 0; j < NPs; ++j) {
      if (i != j) {
        unchange[j] &= eq;
      }
    }
  }
}

int main(int argc, char** argv)
{
  int argi = 1;

  if (argi < argc) {
    printf("%s: No arguments supported!\n", argv[0]);
    return 1;
  }


  // Build variable info (domain and names).
  // Variables are: m_0, m_0', m_1, m_1', ..., m_{N-1}, m_{N-1}'
  PFCtx ctx;
  for (uint i = 0; i < 2*NPs; ++i) {
    char name[10];
    if (i % 2 == 0)
      sprintf(name, "m%u", i / 2);
    else
      sprintf(name, "m%up", i / 2);
    ctx.add(PFVbl(name, 3));
  }

  // Actually create the variables in this context (or manager, if you will).
  ctx.initialize();

  DBog0("Showing all variables");
  print_mvar_list(ctx.mdd_ctx());

  // Ensure every variable but $m_i$ variable does not change.
  // unchange[i] = (m_0=m_0' & m_1=m_1' & ... &
  //                m_{i-1}=m{i-1}' & m_{i+1}=m_{i+1}' &
  //                ... & m_{N-1}=m_{N-1}')
  vector<PF> unchange;
  init_unchanged(unchange, ctx);

  //   m0=0 & (m1=0 | m1=2) & m2=1 --> m1:=1
  PF pf =
    unchange[1] &&
    (ctx.vbl("m0") == 0 &&
     (ctx.vbl("m1") == 0 || ctx.vbl("m1") == 2) &&
     ctx.vbl("m2") == 0 &&
     ctx.vbl("m1p") == 1);

  // Build an array of variables to see (m_0, m_0', m_1, m_1', m_2, m_2').
  array_t* vars = array_alloc(uint, 0);
  array_insert_last(uint, vars, 0); // m_0
  array_insert_last(uint, vars, 1); // m_0'
  array_insert_last(uint, vars, 2); // m_1
  array_insert_last(uint, vars, 3); // m_1'
  array_insert_last(uint, vars, 4); // m_2
  array_insert_last(uint, vars, 5); // m_2'

  mdd_gen* gen;
  array_t* minterm;
  // Show all satisfying valuations of the variables for the formula stored in /acts/
  DBog0("Showing satisfying valuations on m_0, m_0', m_1, m_1', m_2, m_2' of /acts/");
  mdd_t* acts = pf.dup_mdd();
  foreach_mdd_minterm(acts, gen, minterm, vars) {
    for (uint i = 0; i < (uint) minterm->num; ++i) {
      uint x = array_fetch(uint, minterm, i);
      uint vidx = array_fetch(uint, vars, i);
      fprintf(stdout, " %s=%u", ctx.vbl(vidx).name.c_str(), x);
    }
    fputc('\n', stdout);
    array_free(minterm);
  }
  mdd_free(acts);
  array_free(vars);

  return 0;
}

