
#include "test.hh"

#include "cx/table.hh"
#include "inst.hh"
#include "xnsys.hh"
#include <stdio.h>

/**
 * Test dat code.
 */
static void
TestTable()
{
  Cx::Table<uint> t;
  t.push(1);
  t.push(2);
  Claim2_uint( t[1] ,==, 2 );
  Claim2_uint( t[0] ,==, 1 );
}

/**
 * Test dat code.
 */
static void
TestLgTable()
{
  Cx::LgTable<uint> t;
  t.push(1);
  t.push(2);
  Claim2_uint( t[1] ,==, 2 );
  Claim2_uint( t[0] ,==, 1 );
}

/**
 * Test dat code.
 */
static void
TestMakingSumNotTwo()
{
  uint npcs = 5;
  Xn::Net topology;
  Xn::VblSymm* vbl_symm = topology.add_variables("x", npcs, 3);
  Xn::PcSymm* pc_symm = topology.add_processes("P", npcs);

  // Make this f(i) = i-1
  Xn::NatMap indices(npcs);
  for (uint i = 0; i < npcs; ++i) {
    indices.membs[i] = (int)i - 1;
  }
  indices.expression_chunks.push("-1");
  topology.add_read_access(pc_symm, vbl_symm, indices);

  // Now make this f(i) = i
  indices = Xn::NatMap(npcs);
  for (uint i = 0; i < npcs; ++i) {
    indices.membs[i] = (int)i;
  }
  indices.expression_chunks.push("");
  topology.add_write_access(pc_symm, vbl_symm, indices);
}

static void
TestMakingAsymmSumNotTwo()
{
  uint npcs = 5;
  Xn::Net topology;
  Xn::VblSymm* vbl_symm = topology.add_variables("x", npcs, 3);

  // Create a new symmetry for each process.
  for (uint i = 0; i < npcs; ++i) {
    char name[10];
    char idxname[10];
    sprintf(name, "P%u", i);
    Xn::PcSymm* pc_symm = topology.add_processes(name, 1);

    // Make this f(j) = i-1
    Xn::NatMap indices(1);
    indices.membs[0] = (int)i - 1;
    sprintf(idxname, "%d", indices.membs[0]);
    indices.expression_chunks[0] = idxname;
    topology.add_read_access(pc_symm, vbl_symm, indices);

    // Now make this f(j) = i
    indices.membs[0] = (int)i;
    sprintf(idxname, "%d", indices.membs[0]);
    indices.expression_chunks[0] = idxname;
    topology.add_write_access(pc_symm, vbl_symm, indices);
  }
}


/**
 * Test dat code.
 */
void Test()
{
  TestTable();
  TestLgTable();
  TestMakingSumNotTwo();
  TestMakingAsymmSumNotTwo();

  XnSys sys;
  InstMatching(sys, 3);

  XnNet& topo = sys.topology;

  Claim( topo.pcs[1].actUnchanged <= (topo.pfVbl(0, 0) == topo.pfVblPrimed(0, 0)) );
  Claim( topo.pcs[1].actUnchanged <= (topo.pfVbl(2, 0) == topo.pfVblPrimed(2, 0)) );


  XnAct act;
  act.pcIdx = 1;
  act.r0[0] = 1; // Left.
  act.r0[1] = 2; // Right.
  act.w0[0] = 2; // Right.
  act.w1[0] = 0; // Self.

  uint actId = topo.actionIndex(act);
  {
    XnAct action = topo.action(actId);
    Claim2_uint( act.pcIdx ,==, action.pcIdx );
    Claim2_uint( act.r0[0] ,==, action.r0[0] );
    Claim2_uint( act.r0[1] ,==, action.r0[1] );
    Claim2_uint( act.w0[0] ,==, action.w0[0] );
    Claim2_uint( act.w1[0] ,==, action.w1[0] );
  }

  PF actPF =
    topo.pcs[1].actUnchanged &
    ((topo.pfVblR     (1, 0) == 1) &
     (topo.pfVblR     (1, 1) == 2) &
     (topo.pfVbl      (1, 0) == 2) &
     (topo.pfVblPrimed(1, 0) == 0));
  Claim( !actPF.tautology_ck(false) );
  Claim( actPF.equiv_ck(topo.actionPF(actId)) );

  actPF =
    topo.pcs[1].actUnchanged &
    ((topo.pfVbl      (0, 0) == 1) &
     (topo.pfVbl      (2, 0) == 2) &
     (topo.pfVbl      (1, 0) == 2) &
     (topo.pfVblPrimed(1, 0) == 0));
  Claim( actPF.equiv_ck(topo.actionPF(actId)) );


  PF srcPF =
    ((topo.pfVblR(1, 0) == 1) &
     (topo.pfVblR(1, 1) == 2) &
     (topo.pfVbl (1, 0) == 2));
  PF dstPF =
    ((topo.pfVblR(1, 0) == 1) &
     (topo.pfVblR(1, 1) == 2) &
     (topo.pfVbl (1, 0) == 0));
  Claim( (actPF - srcPF).tautology_ck(false) );

  Claim( (dstPF & srcPF).tautology_ck(false) );

  Claim( srcPF <= (actPF.pre() & srcPF) );
  Claim( (actPF.pre() & srcPF).equiv_ck(srcPF) );
  Claim( srcPF.equiv_ck(actPF.pre(dstPF)) );
  {
    Claim( dstPF.equiv_ck(actPF.img(srcPF)) );
    // The rest of this block is actually implied by the first check.
    Claim( dstPF <= actPF.img(srcPF) );
    Claim( actPF.img(srcPF) <= dstPF );
    Claim( actPF.img(srcPF) <= (topo.pfVblR(1, 0) == 1) );
    Claim( actPF.img(srcPF) <= (topo.pfVblR(1, 1) == 2) );
    Claim( actPF.img(srcPF) <= (topo.pfVbl (1, 0) == 0) );
  }
  Claim( dstPF.equiv_ck((actPF & srcPF).img()) );

  Claim( (sys.invariant - sys.invariant).tautology_ck(false) );
  Claim( (sys.invariant | ~sys.invariant).tautology_ck(true) );
  Claim( (srcPF & sys.invariant).tautology_ck(false) );
  Claim( !(dstPF & sys.invariant).tautology_ck(false) );
  Claim( !(~(dstPF & sys.invariant)).tautology_ck(true) );
  Claim( (actPF - srcPF).tautology_ck(false) );

  {
    PF cyclePF =
      ((topo.pfVbl(0, 0) == 1) &
       (topo.pfVblR(0, 0) == 2) &
       (topo.pfVblR(0, 1) == 1) &
       (topo.pfVblPrimed(0, 0) == 0))
      |
      ((topo.pfVbl(0, 0) == 2) &
       (topo.pfVblR(0, 0) == 2) &
       (topo.pfVblR(0, 1) == 1) &
       (topo.pfVblPrimed(0, 0) == 1));
    cyclePF &= topo.pcs[0].actUnchanged;
    Claim( !CycleCk(cyclePF, ~sys.invariant) );

    cyclePF |= 
      ((topo.pfVbl(0, 0) == 0) &
       (topo.pfVblR(0, 0) == 2) &
       (topo.pfVblR(0, 1) == 1) &
       (topo.pfVblPrimed(0, 0) == 2))
      & topo.pcs[0].actUnchanged;
    // All states in the cycle are illegitimate,
    // it should be found.
    Claim( CycleCk(cyclePF, ~sys.invariant) );
  }
}
 
