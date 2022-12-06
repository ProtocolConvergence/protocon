

extern "C" {
  /* #include "cx/syscx.h" */
}

#include "src/cx/synhax.hh"
#include "src/xnsys.hh"
#include "src/inst.hh"

#include "src/namespace.hh"

static
  void
TestXnSys()
{
  Xn::Sys sys;
  InstMatching(sys, 3, false);

  Xn::Net& topo = sys.topology;

  Claim( topo.pcs[1].global_mask_xn <= (topo.pfmla_vbl(0).img_eq(topo.pfmla_vbl(0)) ));
  Claim( topo.pcs[1].global_mask_xn <= (topo.pfmla_vbl(2).img_eq(topo.pfmla_vbl(2)) ));


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

  X::Fmla actPF =
    topo.pcs[1].global_mask_xn &
    ((topo.pfmla_vbl(0) == 1) &
     (topo.pfmla_vbl(1) == 2) &
     (topo.pfmla_vbl(2) == 2) &
     (topo.pfmla_vbl(1).img_eq(0)));
  Claim( !actPF.tautology_ck(false) );
  Claim( !topo.action_pfmla(actidx).tautology_ck(false) );
  Claim( actPF.equiv_ck(topo.action_pfmla(actidx)) );

  P::Fmla srcPF =
    ((topo.pfmla_vbl(0) == 1) &
     (topo.pfmla_vbl(1) == 2) &
     (topo.pfmla_vbl(2) == 2));
  P::Fmla dstPF =
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
    cyclePF &= topo.pcs[0].global_mask_xn;
    Claim( !cyclePF.cycle_ck(~sys.invariant) );

    Claim( !SCC_Find(0, cyclePF, ~sys.invariant) );

    cyclePF |=
      ((topo.pfmla_vbl(0) == 0) &
       (topo.pfmla_vbl(2) == 2) &
       (topo.pfmla_vbl(1) == 1) &
       (topo.pfmla_vbl(0).img_eq(2)))
      & topo.pcs[0].global_mask_xn;
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

  vector<P::Fmla> token_pfmlas(npcs);

  for (uint me = 0; me < npcs; ++me) {
    uint pd = (me + npcs - 1) % npcs;
    const Xn::Pc& pc = topo.pcs[me];

    if (me == npcs-1) {
      topo.pc_symms[1].shadow_pfmla |=
        pc.global_mask_xn &&
        topo.pfmla_vbl(pd) == topo.pfmla_vbl(me) &&
        topo.pfmla_vbl(me).img_eq(IntPFmla(1) - topo.pfmla_vbl(me));
      token_pfmlas[me] = (topo.pfmla_vbl(pd) == topo.pfmla_vbl(me));
    }
    else {
      topo.pc_symms[0].shadow_pfmla |=
        pc.global_mask_xn &&
        topo.pfmla_vbl(pd) != topo.pfmla_vbl(me) &&
        topo.pfmla_vbl(me).img_eq(IntPFmla(1) - topo.pfmla_vbl(me));
      token_pfmlas[me] = (topo.pfmla_vbl(pd) != topo.pfmla_vbl(me));
    }
  }

  sys.shadow_pfmla |= (topo.pc_symms[0].shadow_pfmla | topo.pc_symms[1].shadow_pfmla);

  sys.invariant &= SingleTokenPFmla(token_pfmlas);

  sys.commit_initialization();

  Claim( sys.integrityCk() );
}


END_NAMESPACE

int main() {
  using namespace PROTOCON_NAMESPACE;
  TestXnSys();
  TestTokenRingClosure();
  return 0;
}

