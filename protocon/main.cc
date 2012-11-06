
#include "pf.hh"

#include <stdio.h>
#include "synhax.hh"
#include "xnsys.hh"

int main(int argc, char** argv)
{
  int argi = 1;
  const uint NPs = 6;

  if (argi < argc) {
    printf("%s: No arguments supported!\n", argv[0]);
    return 1;
  }

  // Build a bidirectional ring where each process P_i
  // has variable m_i of domain size 3.
  XnNet topo;
  for (uint i = 0; i < NPs; ++i) {
    char name[10];
    sprintf(name, "m%u", i);

    XnPc& pc = Grow1(topo.pcs);
    pc.addVbl(XnVbl(name, 3));
    pc.addPriv((i+NPs-1) % NPs, 0);
    pc.addPriv((i+1) % NPs, 0);
  }

  // Commit to using this topology.
  // MDD stuff is initialized.
  topo.commitInitialization();

  DBog0("Showing all variables");
  print_mvar_list(topo.pfCtx.mdd_ctx());

  PFCtx& ctx = topo.pfCtx;

  //   m0==0 && (m1==0 || m1==2) && m2==1 --> m1:=1
  //   m0==0 && (m1==0 || m1==2) && m2==1 && m1'==1
  PF pf =
    topo.pcs[1].actUnchanged &&
    (topo.pfVbl(0, 0) == 0 && 
     (topo.pfVbl(1, 0) == 0 || topo.pfVbl(1, 0) == 2) &&
     topo.pfVbl(2, 0) == 0 &&
     topo.pfVblPrimed(1, 0) == 1);

  // Build an array of variable indices to see (m_0, m_0', m_1, m_1', m_2, m_2').
  array_t* vars = array_alloc(uint, 0);
  array_insert_last(uint, vars, topo.pfVbl      (0, 0).idx); // m_0
  array_insert_last(uint, vars, topo.pfVblPrimed(0, 0).idx); // m_0'
  array_insert_last(uint, vars, topo.pfVbl      (1, 0).idx); // m_1
  array_insert_last(uint, vars, topo.pfVblPrimed(1, 0).idx); // m_1'
  array_insert_last(uint, vars, topo.pfVbl      (2, 0).idx); // m_2
  array_insert_last(uint, vars, topo.pfVblPrimed(2, 0).idx); // m_2'

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

