
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

static uint
decmod(uint i, uint by, uint n)
{
  return (i + n - (by % n)) % n;
}

static void
TestPFmla()
{
  Cx::PFmlaCtx ctx;

  const Cx::PFmlaVbl& x = ctx.vbl( ctx.add_vbl("x", 4) );
  const Cx::PFmlaVbl& y = ctx.vbl( ctx.add_vbl("y", 7) );

  Cx::PFmla pf( x == y );

  Claim( Cx::PFmla(true).tautology_ck() );
  Claim( (x == x).tautology_ck() );
  Claim( (x == y).equiv_ck((x == 0 && y == 0) ||
                           (x == 1 && y == 1) ||
                           (x == 2 && y == 2) ||
                           (x == 3 && y == 3)) );

  Claim( (x == y).equiv_ck(y == x) );
  Claim( x.equiv_ck(ctx.vbl("x")) );

  // Add another variable, ensure it doesn't screw up the existing PFmla.
  const Cx::PFmlaVbl& z = ctx.vbl( ctx.add_vbl("z", 5) );
  Claim( pf.equiv_ck(x == y) );
  Claim( pf.overlap_ck(x == z) );
}

static void
TestIntPFmla()
{
  Cx::PFmlaCtx ctx;
  const uint n = 5;
  const Cx::PFmlaVbl& x = ctx.vbl( ctx.add_vbl("x", n) );
  const Cx::PFmlaVbl& y = ctx.vbl( ctx.add_vbl("y", n) );
  const Cx::PFmlaVbl& z = ctx.vbl( ctx.add_vbl("z", n) );

  // Invariant for (game of cards) agreement protocol.
  Cx::PFmla pf( false );
  for (uint a = 0; a < n; ++a) {
    for (uint b = 0; b < n; ++b) {
      // Yeah, this last loop definitely isn't needed.
      // But there's no harm.
      for (uint c = 0; c < n; ++c) {
        if (decmod(a, b, n) == decmod(b, c, n)) {
          pf |= (x == a && y == b && z == c);
        }
      }
    }
  }
  Claim( pf.equiv_ck(((y - x) % n) == ((z - y) % n)) );

  // Invariant for sum-not-(n-1) protocol.
  {
    const uint target = n-1;
    const uint domsz = n;
    pf = true;
    // (x[r-1] + x[r]) % domsz != target
    // Equivalently:
    // For all i,
    for (uint i = 0; i < domsz; ++i) {
      // (x[r-1] == i) implies (x[r] != ((target - i) % domsz))
      pf &= ((x != i) | (y != decmod(target, i, domsz)));
    }
    Claim( pf.equiv_ck(x + y != (int) target) );
  }
}

static void
TestXnSys()
{
  Xn::Sys sys;
  InstMatching(sys, 3, false);

  Xn::Net& topo = sys.topology;

  Claim( topo.pcs[1].act_unchanged_pfmla <= (topo.pfmla_vbl(0).img_eq(topo.pfmla_vbl(0)) ));
  Claim( topo.pcs[1].act_unchanged_pfmla <= (topo.pfmla_vbl(2).img_eq(topo.pfmla_vbl(2)) ));


  Xn::ActSymm act;
  act.pc_symm = &topo.pc_symms[1];
  act.vals.push(1); // Left.
  act.vals.push(2); // Right.
  act.vals.push(2); // Right.
  act.vals.push(0); // Self.

  uint actidx = topo.action_index(act);
  {
    Xn::ActSymm action;
    topo.action(action, actidx);
    Claim2( act.pc_symm ,==, action.pc_symm );
    Claim2_uint( act.vals[0] ,==, action.vals[0] );
    Claim2_uint( act.vals[1] ,==, action.vals[1] );
    Claim2_uint( act.vals[2] ,==, action.vals[2] );
    Claim2_uint( act.vals[3] ,==, action.vals[3] );
  }

  PF actPF =
    topo.pcs[1].act_unchanged_pfmla &
    ((topo.pfmla_vbl(0) == 1) &
     (topo.pfmla_vbl(1) == 2) &
     (topo.pfmla_vbl(2) == 2) &
     (topo.pfmla_vbl(1).img_eq(0)));
  Claim( !actPF.tautology_ck(false) );
  Claim( !topo.action_pfmla(actidx).tautology_ck(false) );
  Claim( actPF.equiv_ck(topo.action_pfmla(actidx)) );

  PF srcPF =
    ((topo.pfmla_vbl(0) == 1) &
     (topo.pfmla_vbl(1) == 2) &
     (topo.pfmla_vbl(2) == 2));
  PF dstPF =
    ((topo.pfmla_vbl(0) == 1) &
     (topo.pfmla_vbl(1) == 0) &
     (topo.pfmla_vbl(2) == 2));
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
    Claim( actPF.img(srcPF) <= (topo.pfmla_vbl(0) == 1) );
    Claim( actPF.img(srcPF) <= (topo.pfmla_vbl(1) == 0) );
    Claim( actPF.img(srcPF) <= (topo.pfmla_vbl(2) == 2) );
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
      ((topo.pfmla_vbl(0) == 1) &
       (topo.pfmla_vbl(2) == 2) &
       (topo.pfmla_vbl(1) == 1) &
       (topo.pfmla_vbl(0).img_eq(0)))
      |
      ((topo.pfmla_vbl(0) == 2) &
       (topo.pfmla_vbl(2) == 2) &
       (topo.pfmla_vbl(1) == 1) &
       (topo.pfmla_vbl(0).img_eq(1)));
    cyclePF &= topo.pcs[0].act_unchanged_pfmla;
    Claim( !CycleCk(cyclePF, ~sys.invariant) );

    cyclePF |= 
      ((topo.pfmla_vbl(0) == 0) &
       (topo.pfmla_vbl(2) == 2) &
       (topo.pfmla_vbl(1) == 1) &
       (topo.pfmla_vbl(0).img_eq(2)))
      & topo.pcs[0].act_unchanged_pfmla;
    // All states in the cycle are illegitimate,
    // it should be found.
    Claim( CycleCk(cyclePF, ~sys.invariant) );
  }
}

/**
 * Test dat code.
 */
void Test()
{
  TestTable();
  TestLgTable();
  TestPFmla();
  TestIntPFmla();
  TestXnSys();
}
 
