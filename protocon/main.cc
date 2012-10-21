
#include "mdd.h"

#include <stdio.h>
#include "synhax.hh"

#define NPs 6

  void
mdd_assign(mdd_t** a, mdd_t* b)
{
  if (*a)  mdd_free(*a);
  *a = b;
}

  void
init_unchanged(mdd_t** unchange, mdd_manager* ctx)
{
  for (uint i = 0; i < NPs; ++i) {
    unchange[i] = 0; 
  }
  for (uint i = 0; i < NPs; ++i) {
    mdd_t* eq = mdd_eq(ctx, 2*i+0, 2*i+1);
    for (uint j = 0; j < NPs; ++j) {
      if (i == j)
        continue;
      if (unchange[j])
        mdd_assign(&unchange[j], mdd_and(unchange[j], eq, 1, 1));
      else
        unchange[j] = mdd_dup(eq);
    }
    mdd_free(eq);
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
  char namebufs[2*NPs][10];
  array_t* doms = array_alloc(uint, 0);
  array_t* names = array_alloc(char*, 0);
  for (uint i = 0; i < 2*NPs; ++i) {
    array_insert_last(uint, doms, 3);
    if (i % 2 == 0)
      sprintf(namebufs[i], "m%u", i / 2);
    else
      sprintf(namebufs[i], "m%up", i / 2);
    array_insert_last(char*, names, namebufs[i]);
  }

  // Actually create the variables in this context (or manager, if you will).
  mdd_manager* ctx = mdd_init_empty();
  mdd_create_variables(ctx, doms, names, 0);

  // Ensure every variable but $m_i$ variable does not change.
  // unchange[i] = (m_0=m_0' & m_1=m_1' & ... &
  //                m_{i-1}=m{i-1}' & m_{i+1}=m_{i+1}' &
  //                ... & m_{N-1}=m_{N-1}')
  mdd_t* unchange[NPs];
  init_unchanged(unchange, ctx);

  DBog0("Showing all variables");
  print_mvar_list(ctx);


  // Build an array of variables to see (m_0, m_0', m_2, m_2').
  array_t* vars = array_alloc(uint, 0);
  array_insert_last(uint, vars, 0); // m_0
  array_insert_last(uint, vars, 1); // m_0'
  array_insert_last(uint, vars, 4); // m_2
  array_insert_last(uint, vars, 5); // m_2'

  mdd_gen* gen;
  array_t* minterm;
  // Show all satisfying valuations of the variables for the formula stored in /unchange[0]/.
  DBog0("Showing satisfying valuations on m_0, m_0', m_2, m_2' of unchanged[0]");
  foreach_mdd_minterm(unchange[0], gen, minterm, vars) {
    for (uint i = 0; i < (uint) minterm->num; ++i) {
      uint x = array_fetch(uint, minterm, i);
      uint vidx = array_fetch(uint, vars, i);
      fprintf(stdout, " %s=%u", namebufs[vidx], x);
    }
    fputc('\n', stdout);
    array_free(minterm);
  }

  for (uint i = 0; i < ArraySz( unchange ); ++i) {
    mdd_free(unchange[i]);
  }

  mdd_quit(ctx);
  array_free(doms);
  array_free(names);
  array_free(vars);

  return 0;
}

