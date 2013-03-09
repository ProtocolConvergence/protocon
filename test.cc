
#include "test.hh"

#include "cx/table.hh"
#include "inst.hh"
#include "xnsys.hh"

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
void Test()
{
  TestTable();
  TestLgTable();

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
  Claim( !actPF.tautologyCk(false) );
  Claim( actPF.equivCk(topo.actionPF(actId)) );

  actPF =
    topo.pcs[1].actUnchanged &
    ((topo.pfVbl      (0, 0) == 1) &
     (topo.pfVbl      (2, 0) == 2) &
     (topo.pfVbl      (1, 0) == 2) &
     (topo.pfVblPrimed(1, 0) == 0));
  Claim( actPF.equivCk(topo.actionPF(actId)) );


  PF srcPF =
    ((topo.pfVblR(1, 0) == 1) &
     (topo.pfVblR(1, 1) == 2) &
     (topo.pfVbl (1, 0) == 2));
  PF dstPF =
    ((topo.pfVblR(1, 0) == 1) &
     (topo.pfVblR(1, 1) == 2) &
     (topo.pfVbl (1, 0) == 0));
  Claim( (actPF - srcPF).tautologyCk(false) );

  Claim( (dstPF & srcPF).tautologyCk(false) );

  Claim( srcPF <= (topo.preimage(actPF) & srcPF) );
  Claim( (topo.preimage(actPF) & srcPF).equivCk(srcPF) );
  Claim( srcPF.equivCk(topo.preimage(actPF, dstPF)) );
  {
    Claim( dstPF.equivCk(topo.image(actPF, srcPF)) );
    // The rest of this block is actually implied by the first check.
    Claim( dstPF <= topo.image(actPF, srcPF) );
    Claim( topo.image(actPF, srcPF) <= dstPF );
    Claim( topo.image(actPF, srcPF) <= (topo.pfVblR(1, 0) == 1) );
    Claim( topo.image(actPF, srcPF) <= (topo.pfVblR(1, 1) == 2) );
    Claim( topo.image(actPF, srcPF) <= (topo.pfVbl (1, 0) == 0) );
  }
  Claim( dstPF.equivCk(topo.image(actPF & srcPF)) );

  Claim( (sys.invariant - sys.invariant).tautologyCk(false) );
  Claim( (sys.invariant | ~sys.invariant).tautologyCk(true) );
  Claim( (srcPF & sys.invariant).tautologyCk(false) );
  Claim( !(dstPF & sys.invariant).tautologyCk(false) );
  Claim( !(~(dstPF & sys.invariant)).tautologyCk(true) );
  Claim( (actPF - srcPF).tautologyCk(false) );

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
    Claim( !CycleCk(topo, cyclePF, ~sys.invariant) );

    cyclePF |= 
      ((topo.pfVbl(0, 0) == 0) &
       (topo.pfVblR(0, 0) == 2) &
       (topo.pfVblR(0, 1) == 1) &
       (topo.pfVblPrimed(0, 0) == 2))
      & topo.pcs[0].actUnchanged;
    // All states in the cycle are illegitimate,
    // it should be found.
    Claim( CycleCk(topo, cyclePF, ~sys.invariant) );
  }
}
 
