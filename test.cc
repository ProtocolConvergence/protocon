
#include "test.hh"

#include "cx/synhax.hh"

extern "C" {
#include "cx/sesp.h"
}
#include "cx/alphatab.hh"
#include "cx/map.hh"
#include "cx/set.hh"
#include "cx/table.hh"
#include "inst.hh"
#include "xnsys.hh"
#include "protoconfile.hh"
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

static void
TestFlatSet()
{
  Cx::Table<uint> tab_b;
  tab_b.push(3);
  tab_b.push(2);
  tab_b.push(7);
  tab_b.push(11);
  tab_b.push(4);
  tab_b.push(6);
  tab_b.push(15);
  tab_b.push(0);

  Cx::Set<uint> set_b(tab_b);
  Cx::FlatSet<uint> flat_a( tab_b );
  Claim( flat_a.elem_ck(3) );
  Claim( flat_a.elem_ck(15) );

  {
    Cx::FlatSet<uint> flat_b( tab_b );
    Claim( flat_a.subseteq_ck(flat_b) );
    Claim( flat_b.subseteq_ck(flat_a) );
  }
  set_b |= 50;
  {
    Cx::FlatSet<uint> flat_b( set_b );
    Claim( flat_a.subseteq_ck(flat_b) );
    Claim( !flat_b.subseteq_ck(flat_a) );
  }
  set_b -= Set<uint>(50);
  set_b |= 10;
  {
    Cx::FlatSet<uint> flat_b( set_b );
    Claim( flat_a.subseteq_ck(flat_b) );
    Claim( !flat_b.subseteq_ck(flat_a) );
  }
}

static void
TestPFmla()
{
  Cx::PFmlaCtx ctx;

  const Cx::PFmlaVbl& w = ctx.vbl( ctx.add_vbl("w", 4) );
  const Cx::PFmlaVbl& x = ctx.vbl( ctx.add_vbl("x", 4) );
  const Cx::PFmlaVbl& y = ctx.vbl( ctx.add_vbl("y", 7) );

  uint w_list_id = ctx.add_vbl_list();
  uint x_list_id = ctx.add_vbl_list();
  ctx.add_to_vbl_list(w_list_id, id_of(w));
  ctx.add_to_vbl_list(x_list_id, id_of(x));

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

  // Ensure substitution smooths the source variables.
  Cx::PFmla pf_a = (w == 2);
  Cx::PFmla pf_b = (x == 2);

  Claim( !pf_a.equiv_ck(pf_b) );
  pf = pf_b.substitute_new_old(w_list_id, x_list_id);
  Claim( pf.equiv_ck(pf_a) );
  pf = pf_a.substitute_new_old(x_list_id, w_list_id);
  Claim( pf.equiv_ck(pf_b) );

  // Test picking.
  pf = (x == y).pick_pre();
  Claim2( pf ,<=, (x == y) );
  Claim( !pf.equiv_ck(x == y) );
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

  Cx::PFmla actPF =
    topo.pcs[1].act_unchanged_pfmla &
    ((topo.pfmla_vbl(0) == 1) &
     (topo.pfmla_vbl(1) == 2) &
     (topo.pfmla_vbl(2) == 2) &
     (topo.pfmla_vbl(1).img_eq(0)));
  Claim( !actPF.tautology_ck(false) );
  Claim( !topo.action_pfmla(actidx).tautology_ck(false) );
  Claim( actPF.equiv_ck(topo.action_pfmla(actidx)) );

  Cx::PFmla srcPF =
    ((topo.pfmla_vbl(0) == 1) &
     (topo.pfmla_vbl(1) == 2) &
     (topo.pfmla_vbl(2) == 2));
  Cx::PFmla dstPF =
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
    Cx::PFmla cyclePF =
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
    Claim( !cyclePF.cycle_ck(~sys.invariant) );

    Claim( !SCC_Find(0, cyclePF, ~sys.invariant) );

    cyclePF |=
      ((topo.pfmla_vbl(0) == 0) &
       (topo.pfmla_vbl(2) == 2) &
       (topo.pfmla_vbl(1) == 1) &
       (topo.pfmla_vbl(0).img_eq(2)))
      & topo.pcs[0].act_unchanged_pfmla;
    // All states in the cycle are illegitimate,
    // it should be found.
    Claim( cyclePF.cycle_ck(~sys.invariant) );

    Claim( SCC_Find(0, cyclePF, ~sys.invariant) );
  }
}

static void
TestTokenRingClosure()
{
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;
  const uint npcs = 4;
  UnidirectionalRing(topo, npcs, 2, "b", true, true);

  vector<Cx::PFmla> token_pfmlas(npcs);

  for (uint me = 0; me < npcs; ++me) {
    uint pd = (me + npcs - 1) % npcs;
    const Xn::Pc& pc = topo.pcs[me];

    if (me == npcs-1) {
      topo.pc_symms[1].shadow_pfmla |=
        pc.act_unchanged_pfmla &&
        topo.pfmla_vbl(pd) == topo.pfmla_vbl(me) &&
        topo.pfmla_vbl(me).img_eq(Cx::IntPFmla(1) - topo.pfmla_vbl(me));
      token_pfmlas[me] = (topo.pfmla_vbl(pd) == topo.pfmla_vbl(me));
    }
    else {
      topo.pc_symms[0].shadow_pfmla |=
        pc.act_unchanged_pfmla &&
        topo.pfmla_vbl(pd) != topo.pfmla_vbl(me) &&
        topo.pfmla_vbl(me).img_eq(Cx::IntPFmla(1) - topo.pfmla_vbl(me));
      token_pfmlas[me] = (topo.pfmla_vbl(pd) != topo.pfmla_vbl(me));
    }
  }

  sys.shadow_pfmla |= (topo.pc_symms[0].shadow_pfmla | topo.pc_symms[1].shadow_pfmla);

  sys.invariant &= SingleTokenPFmla(token_pfmlas);

  sys.commit_initialization();

  Claim( sys.integrityCk() );
}

void TestProtoconFile(bool agreement)
{
  Xn::Sys sys_f; //< From file.
  Xn::Sys sys_c; //< From code.

  Xn::Net& topo_f = sys_f.topology;
  Xn::Net& topo_c = sys_c.topology;

  topo_c.pfmla_ctx.use_context_of(topo_f.pfmla_ctx);

  Cx::PFmla pf;

  ProtoconFileOpt infile_opt;
  if (agreement)
    infile_opt.file_path = "inst/Agreement.protocon";
  else
    infile_opt.file_path = "inst/SumNotTwo.protocon";
  ReadProtoconFile(sys_f, infile_opt);

  uint npcs = topo_f.pcs.sz();
  Claim2( npcs ,>=, 3 );

  if (agreement)
    InstAgreementRing(sys_c, npcs, "y");
  else
    InstSumNot(sys_c, npcs, 3, 2, "y");

  Claim2( topo_f.pcs.sz()  ,==, topo_c.pcs.sz() );
  Claim2( topo_f.vbls.sz() ,==, topo_c.vbls.sz() );
  Claim2( topo_f.pc_symms[0].wmap ,==, topo_c.pc_symms[0].wmap );

  Claim( !sys_f.invariant.equiv_ck(sys_c.invariant) );

  pf = sys_c.invariant;
  pf = pf.substitute_new_old(topo_f.vbl_symms[0].pfmla_list_id,
                             topo_c.vbl_symms[0].pfmla_list_id);
  Claim( pf.equiv_ck(sys_f.invariant) );

  topo_c.pfmla_ctx.nullify_context();
}

/**
 * Test dat code.
 */
void Test()
{
  TestTable();
  TestLgTable();
  TestFlatSet();
  TestPFmla();
  TestIntPFmla();
  TestXnSys();
  TestTokenRingClosure();
  TestProtoconFile(true);
  TestProtoconFile(false);
}

