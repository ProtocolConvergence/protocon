
extern "C" {
#include "cx/syscx.h"
}

#include "cx/synhax.hh"

extern "C" {
#include "cx/fileb.h"
#include "cx/sesp.h"
}
#include "cx/alphatab.hh"
#include "cx/map.hh"
#include "cx/set.hh"
#include "cx/table.hh"
#include "inst.hh"
#include "xnsys.hh"
#include "conflictfamily.hh"
#include "prot-xfile.hh"
#include "stabilization.hh"
#include "kautz.hh"
#include "search.hh"
#include "synthesis.hh"
#include <stdio.h>

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

  // Ensure the action (x < y --> x:=y; y:=x;)
  // can be specified using img_eq(IntPFmla).
  pf = (x < y);
  Cx::IntPFmla ipf;
  ipf = y;  pf &= x.img_eq(ipf);
  ipf = x;  pf &= y.img_eq(ipf);
  for (uint a = 0; a < n; ++a) {
    for (uint b = 0; b < n; ++b) {
      if (a < b) {
        Claim( ((x == b) & (y == a)).equiv_ck(pf.img((x == a) & (y == b))) );
      }
      else {
        Claim( !pf.img((x == a) & (y == b)).sat_ck() );
      }
    }
  }
}

static void
TestConflictFamily()
{
  ConflictFamily conflicts;
  Cx::LgTable< Set<uint> > delsets;

  delsets.grow1() <<  0 <<  1 <<  3;
  delsets.grow1() <<  5 <<  1 <<  3;
  delsets.grow1() <<  7 <<  1 <<  3;
  delsets.grow1() << 11 <<  1 <<  3;
  delsets.grow1() << 14 << 15 <<  1 << 3;
  delsets.grow1() << 14 << 17 <<  1 << 3;
  for (uint i = 0; i < delsets.sz(); ++i)
    conflicts.add_conflict(delsets[i]);

  Set<uint> action_set;
  action_set << 1 << 3 << 2 << 16 << 20;
  Set<uint> candidate_set;
  candidate_set << 5 << 0 << 14 << 17;

  Set<uint> membs;
  bool good =
    conflicts.conflict_membs(&membs, FlatSet<uint>(action_set),
                             FlatSet<uint>(candidate_set));
  Claim( good );
  Claim( membs.elem_ck(5) );
  Claim( membs.elem_ck(0) );
  Claim( !membs.elem_ck(7) );
  Claim( !membs.elem_ck(14) );
  Claim( !membs.elem_ck(15) );
  Claim( !membs.elem_ck(17) );

  candidate_set -= membs;
  membs.clear();
  good =
    conflicts.conflict_membs(&membs, FlatSet<uint>(action_set),
                             FlatSet<uint>(candidate_set));
  Claim( good );
  Claim( membs.empty() );

  conflicts.add_conflict( Set<uint>() << 1 << 3 << 16 );
  good =
    conflicts.conflict_membs(&membs, FlatSet<uint>(action_set),
                             FlatSet<uint>(candidate_set));
  Claim( !good );
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
    X::Fmla cyclePF =
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

static void
TestProtoconFile(bool agreement)
{
  Xn::Sys sys_f; //< From file.
  Xn::Sys sys_c; //< From code.

  Xn::Net& topo_f = sys_f.topology;
  Xn::Net& topo_c = sys_c.topology;

  topo_c.pfmla_ctx.use_context_of(topo_f.pfmla_ctx);

  Cx::PFmla pf;

  const char* filename;
  if (agreement)
    filename = "examplespec/LeaderRingHuang.prot";
  else
    filename = "examplespec/SumNotTwo.prot";

  ProtoconFileOpt infile_opt;
  infile_opt.text = textfile_AlphaTab (0, filename);

  if (!ReadProtoconFile(sys_f, infile_opt)) {
    Claim( 0 && "Can't parse file" );
  }

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
}

static void
TestProtoconFileSumNotTwo()
{
  TestProtoconFile(false);
}

static void
TestProtoconFileAgreement()
{
  TestProtoconFile(true);
}

static void
SetupSilentShadowRing(Xn::Sys& sys, const uint npcs,
                      const char* puppet_vbl_name, const uint puppet_vbl_domsz,
                      const char* shadow_vbl_name, const uint shadow_vbl_domsz)
{
  Xn::Net& topo = sys.topology;
  topo.add_variables(puppet_vbl_name, npcs, puppet_vbl_domsz, Xn::Vbl::Puppet);
  topo.add_variables(shadow_vbl_name, npcs, shadow_vbl_domsz, Xn::Vbl::Shadow);
  Xn::PcSymm* pc_symm = topo.add_processes("P", "i", npcs);
  Xn::NatMap indices(npcs);

  for (uint i = 0; i < npcs; ++i)
    indices.membs[i] = (int)i - 1;
  indices.expression = "i-1";
  topo.add_read_access(pc_symm, &topo.vbl_symms[0], indices);

  for (uint i = 0; i < npcs; ++i)
    indices.membs[i] = (int)i;
  indices.expression = "i";
  topo.add_write_access(pc_symm, &topo.vbl_symms[0], indices);

  for (uint i = 0; i < npcs; ++i)
    indices.membs[i] = (int)i + 1;
  indices.expression = "i+1";
  topo.add_read_access(pc_symm, &topo.vbl_symms[0], indices);

  for (uint i = 0; i < npcs; ++i)
    indices.membs[i] = (int)i;
  indices.expression = "i";
  topo.add_write_access(pc_symm, &topo.vbl_symms[1], indices);

  sys.spec->invariant_style = Xn::FutureAndShadow;
  sys.spec->invariant_scope = Xn::ShadowInvariant;
  sys.commit_initialization();
}

static void
TestShadowColorRing()
{
  Cx::OFile& of = DBogOF;
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;
  const uint npcs = 3;
  SetupSilentShadowRing(sys, npcs, "x", 3, "c", 3);

  for (uint i = 0; i < npcs; ++i) {
    sys.invariant &=
      (topo.pfmla_vbl(*topo.vbl_symms[1].membs[i])
       !=
       topo.pfmla_vbl(*topo.vbl_symms[1].membs[umod_int(i+1, npcs)]));
  }

  static const uint act_vals[][4] = {
    // x[i-1] x[i] x[i+1] --> x[i]'
    { 0, 0, 0, 1 },
    { 0, 0, 1, 1 },
    { 0, 0, 2, 1 },
    { 0, 2, 0, 2 },
    { 0, 2, 1, 2 },
    { 0, 2, 2, 1 },
    { 1, 0, 0, 0 },
    { 1, 1, 0, 2 },
    { 1, 1, 1, 0 },
    { 1, 1, 2, 0 },
    { 1, 2, 1, 2 },
    { 1, 2, 2, 0 },
    { 2, 0, 0, 0 },
    { 2, 0, 1, 0 },
    { 2, 1, 0, 1 },
    { 2, 1, 1, 1 },
    { 2, 1, 2, 1 },
    { 2, 2, 0, 2 },
    { 2, 2, 1, 2 },
    { 2, 2, 2, 0 }
  };

  for (uint actidx = 0; actidx < topo.n_possible_acts; ++actidx)
  {
    Xn::ActSymm act_symm;
    topo.action(act_symm, actidx);

    bool add_action = false;
    for (uint i = 0; i < ArraySz(act_vals) && !add_action; ++i) {
      add_action =
        (   act_vals[i][0] == act_symm.guard(0)
         && (   act_vals[i][1] == act_symm.guard(1)
             || act_vals[i][3] == act_symm.guard(1))
         && act_vals[i][2] == act_symm.guard(2)
         && act_vals[i][3] == act_symm.assign(0)
         && act_vals[i][3] == act_symm.assign(1));
    }

    if (add_action)
    {
      uint rep_actidx = topo.representative_action_index(actidx);
      if (rep_actidx == actidx)
        sys.actions.push_back(actidx);
    }
  }

  StabilizationOpt stabilization_opt;
  if (!stabilization_ck(of, sys, stabilization_opt, sys.actions)) {
    Claim(0);
  }
}

static void
TestShadowMatchRing()
{
  Cx::OFile& ofile = DBogOF;
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;
  const uint npcs = 3;
  SetupSilentShadowRing(sys, npcs, "x", 2, "m", 3);

  const Cx::PFmlaVbl& x0 = topo.pfmla_vbl(*topo.vbl_symms[0].membs[0]);
  const Cx::PFmlaVbl& x1 = topo.pfmla_vbl(*topo.vbl_symms[0].membs[1]);
  const Cx::PFmlaVbl& x2 = topo.pfmla_vbl(*topo.vbl_symms[0].membs[2]);
  const Cx::PFmlaVbl& m0 = topo.pfmla_vbl(*topo.vbl_symms[1].membs[0]);
  const Cx::PFmlaVbl& m1 = topo.pfmla_vbl(*topo.vbl_symms[1].membs[1]);
  const Cx::PFmlaVbl& m2 = topo.pfmla_vbl(*topo.vbl_symms[1].membs[2]);

  sys.invariant
    =  (m0==2 && m1==0 && m2==1)
    || (m0==0 && m1==1 && m2==2)
    || (m0==1 && m1==2 && m2==0)
    ;

  Xn::ActSymm act;
  act.pc_symm = &topo.pc_symms[0];
  act.vals.grow(6, 0);
  act.vals[0] = 1;  Claim2( 1 ,==, act.guard(0) );
  act.vals[1] = 1;  Claim2( 1 ,==, act.aguard(0) );
  act.vals[2] = 1;  Claim2( 1 ,==, act.guard(2) );
  act.vals[3] = 0;
  act.vals[4] = 0;  Claim2( 0 ,==, act.assign(0) );
  act.vals[5] = 0;  Claim2( 0 ,==, act.assign(1) );

  uint actidx = topo.action_index(act);
  actidx = topo.representative_action_index(actidx);
  X::Fmla act_xn = topo.action_pfmla(actidx);

  X::Fmla expect_xn =
    x0==1 && x1==1 && x2==1
    &&
    ((x0.img_eq(0) && x1.img_eq(x1) && x2.img_eq(x2) &&
      m0.img_eq(0) && m1.img_eq(m1) && m2.img_eq(m2))
     ||
     (x0.img_eq(x0) && x1.img_eq(0) && x2.img_eq(x2) &&
      m0.img_eq(m0) && m1.img_eq(0) && m2.img_eq(m2))
     ||
     (x0.img_eq(x0) && x1.img_eq(x1) && x2.img_eq(0) &&
      m0.img_eq(m0) && m1.img_eq(m1) && m2.img_eq(0))
    );
  Claim( expect_xn.equiv_ck(act_xn) );

  act.vals[0] = 0;  act.vals[1] = 1;  act.vals[2] = 0;
  act.vals[3] = 0; // m[i] ignored
  act.vals[4] = 1; // x[i] remains the same
  act.vals[5] = 2; // m[i]:=2

  actidx = topo.action_index(act);
  actidx = topo.representative_action_index(actidx);
  act_xn = topo.action_pfmla(actidx);
  expect_xn =
    x0.img_eq(x0) && x1.img_eq(x1) && x2.img_eq(x2) &&
    ((x0==1 && x1==0 && x2==0 && m0!=2 &&
      m0.img_eq(2) && m1.img_eq(m1) && m2.img_eq(m2))
     ||
     (x0==0 && x1==1 && x2==0 && m1!=2 &&
      m0.img_eq(m0) && m1.img_eq(2) && m2.img_eq(m2))
     ||
     (x0==0 && x1==0 && x2==1 && m2!=2 &&
      m0.img_eq(m0) && m1.img_eq(m1) && m2.img_eq(2))
    );
  Claim( expect_xn.equiv_ck(act_xn) );

  const uint init_actions[][5] = {
    { 0, 0, 0, 1, 2 },
    { 1, 1, 1, 0, 0 },
    { 0, 0, 1, 0, 1 },
    { 1, 0, 0, 0, 0 }
  };
  for (uint i = 0; i < ArraySz(init_actions); ++i) {
    act.vals[0] = init_actions[i][0];
    act.vals[1] = init_actions[i][1];
    act.vals[2] = init_actions[i][2];
    act.vals[3] = 0;
    act.vals[4] = init_actions[i][3];
    act.vals[5] = init_actions[i][4];
    actidx = topo.action_index(act);
    actidx = topo.representative_action_index(actidx);
    sys.actions.push_back(actidx);
  }

  {
    Xn::ActSymm act1;
    Xn::ActSymm act2;
    act1.pc_symm = &topo.pc_symms[0];
    act2.pc_symm = &topo.pc_symms[0];
    act1.vals << 0 << 0 << 0 << 0 << 1 << 2;
    act2.vals << 0 << 1 << 0 << 0 << 1 << 2;
    Claim( coexist_ck(act1, act2) );
  }

  AddConvergenceOpt opt;
  opt.randomize_pick = false;
  opt.max_height = 0;
  opt.log = &ofile;
  bool solution_found = AddStabilization(sys, opt);
  Claim( solution_found );
}


static void TestProbabilisticLivelock()
{
  Xn::Sys sys;
  ProtoconFileOpt infile_opt;
  infile_opt.text = textfile_AlphaTab (0, "examplesoln/ColorUniRing.prot");

  if (!ReadProtoconFile(sys, infile_opt)) {
    Claim( 0 && "Can't parse file" );
  }

  Xn::Net& topo = sys.topology;
  X::Fmlae xn(&sys.topology.xfmlae_ctx);
  for (uint i = 0; i < topo.pcs.sz(); ++i) {
    const Xn::Pc& pc = topo.pcs[i];
    xn[i] = pc.puppet_xn;
  }

  P::Fmla scc(false);
  P::Fmla assumed = sys.closed_assume;

  bool cycle_found =
#if 1
    xn.probabilistic_livelock_ck(&scc, assumed)
#elif 0
    xn.cycle_ck(&scc, 0, 0, &assumed)
#else
    sys.direct_pfmla.cycle_ck(&scc, 0, 0, &assumed)
#endif
    ;

  Claim(scc.subseteq_ck(sys.invariant));
  Claim(!cycle_found);
}

static void
TestOPutKautz()
{
  Cx::OFile ofile( stdout_OFile () );
  oput_graphviz_kautz(ofile, 4, 25);
}

static void TestTestOrder();
static void TestAll();

struct TestInfo
{
  const char* name;
  void (*fn) ();
};

static int CmpTestInfo(const void* a, const void* b)
{
  return strcmp(((TestInfo*)a)->name, ((TestInfo*)b)->name);
}

#define W(testname)  ,{ Stringify(testname), Test##testname }
static const TestInfo AllTests[] = {
  { "", TestAll }
#include "testlist.h"
};
#undef W

void TestTestOrder()
{
  for (uint i = 1; i < ArraySz(AllTests); ++i)
    Claim2( 0 ,>, CmpTestInfo(&AllTests[i-1], &AllTests[i]) );
}

void TestAll()
{
  for (uint i = 1; i < ArraySz(AllTests); ++i)
    AllTests[i].fn();
}

static void Test(const char testname[])
{
  TestInfo key;
  key.name = testname;
  key.fn = 0;
  const TestInfo* t = (TestInfo*) bsearch
    (&key, AllTests, ArraySz(AllTests), sizeof(AllTests[0]), CmpTestInfo);
  Claim( t );
  t->fn();
}


int main(int argc, char** argv)
{
  int argi = (init_sysCx (&argc, &argv), 1);

  if (argi == argc) {
    TestAll();
  }
  else {
    while (argi < argc) {
      Test(argv[argi++]);
    }
  }

  lose_sysCx ();
  return 0;
}

