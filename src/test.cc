
#define TestClaim

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
#include "prot-xfile.hh"
#include "stabilization.hh"
#include "cx/kautz.hh"
#include "search.hh"
#include "synthesis.hh"
#include <stdio.h>

#include "test-pcxn.hh"

#include "namespace.hh"

static void
TestXFmlae()
{
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;

  P::Fmla pf;

  const char* filename = "examplespec/SumNotTwo.prot";

  ProtoconFileOpt infile_opt;
  infile_opt.text.moveq
    (textfile_AlphaTab (0, filename));

  topo.lightweight = true;

  if (!ReadProtoconFile(sys, infile_opt)) {
    Claim( 0 && "Can't parse file" );
  }

  Xn::ActSymm act;
  topo.action(act, 0);
  act.vals[0] = 2;
  act.vals[1] = 0;
  act.vals[2] = 1;
  uint actidx = topo.action_index(act);

  Claim( topo.action_pfmla(actidx).pre().equiv_ck
         (topo.action_xfmlae(actidx).pre()) );
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

static void
TestProtoconFile(bool agreement)
{
  Xn::Sys sys_f; //< From file.
  Xn::Sys sys_c; //< From code.

  Xn::Net& topo_f = sys_f.topology;
  Xn::Net& topo_c = sys_c.topology;

  topo_c.pfmla_ctx.use_context_of(topo_f.pfmla_ctx);

  P::Fmla pf;

  const char* filename;
  if (agreement)
    filename = "examplespec/LeaderRingHuang.prot";
  else
    filename = "examplespec/SumNotTwo.prot";

  ProtoconFileOpt infile_opt;
  infile_opt.text.moveq
    (textfile_AlphaTab (0, filename));

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
  Claim2( topo_f.pc_symms[0].spec->wmap ,==, topo_c.pc_symms[0].spec->wmap );

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
  topo.add_variables(puppet_vbl_name, npcs, puppet_vbl_domsz, Xn::Puppet);
  topo.add_variables(shadow_vbl_name, npcs, shadow_vbl_domsz, Xn::Shadow);
  Xn::PcSymm* pc_symm = topo.add_processes("P", "i", npcs);
  Xn::NatMap indices(npcs);

  for (uint i = 0; i < npcs; ++i)
    indices.membs[i] = (int)i - 1;
  indices.expression = "i-1";
  topo.add_access(pc_symm, &topo.vbl_symms[0], indices, Xn::ReadAccess);

  for (uint i = 0; i < npcs; ++i)
    indices.membs[i] = (int)i;
  indices.expression = "i";
  topo.add_access(pc_symm, &topo.vbl_symms[0], indices, Xn::WriteAccess);

  for (uint i = 0; i < npcs; ++i)
    indices.membs[i] = (int)i + 1;
  indices.expression = "i+1";
  topo.add_access(pc_symm, &topo.vbl_symms[0], indices, Xn::ReadAccess);

  for (uint i = 0; i < npcs; ++i)
    indices.membs[i] = (int)i;
  indices.expression = "i";
  topo.add_access(pc_symm, &topo.vbl_symms[1], indices, Xn::WriteAccess);

  sys.spec->invariant_style = Xn::FutureAndShadow;
  sys.spec->invariant_scope = Xn::ShadowInvariant;
  sys.commit_initialization();
}

static void
TestShadowColorRing()
{
  OFile& of = DBogOF;
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
  OFile& ofile = DBogOF;
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;
  const uint npcs = 3;
  SetupSilentShadowRing(sys, npcs, "x", 2, "m", 3);

  const PFmlaVbl& x0 = topo.pfmla_vbl(*topo.vbl_symms[0].membs[0]);
  const PFmlaVbl& x1 = topo.pfmla_vbl(*topo.vbl_symms[0].membs[1]);
  const PFmlaVbl& x2 = topo.pfmla_vbl(*topo.vbl_symms[0].membs[2]);
  const PFmlaVbl& m0 = topo.pfmla_vbl(*topo.vbl_symms[1].membs[0]);
  const PFmlaVbl& m1 = topo.pfmla_vbl(*topo.vbl_symms[1].membs[1]);
  const PFmlaVbl& m2 = topo.pfmla_vbl(*topo.vbl_symms[1].membs[2]);

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
    Claim( coexist_ck(act1, act2, topo) );
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
  infile_opt.text.moveq
    (textfile_AlphaTab (0, "examplesoln/ColorUniRing.prot"));

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
  OFile ofile( stdout_OFile () );
  oput_graphviz_kautz(ofile, 4, 25);
}

static
  void
Test(const char testname[])
{
  void (*fn) () = 0;

  /* cswitch testname
   *   -case-pfx "fn = Test"
   *   -array AllTests
   *   -x testlist.txt
   *   -o test-dep/switch.c
   */
#include "test-dep/switch.c"

  if (fn) {
    fn();
  }
  else if (!testname[0]) {
    for (uint i = 0; i < ArraySz(AllTests); ++i) {
      Test(AllTests[i]);
    }
  }
  else {
    Claim( 0 && "Test does not exist." );
  }
}

static void
TestUDP()
{
  // Case: BOTH disabled
  // # If I receive a message that has the wrong sequence number for me,
  // then SEND using my sequence number as {src_seq}
  // # If I receieve a message that uses my correct sequence number,
  // but I don't recognize the other's sequence number,
  // then SEND.
  // # If I don't receive a message after some timeout,
  // then SEND.

  // Case: I am disabled, neighbor is enabled to act.
  // # If I get a message with a positive {enabled} value,
  // then SEQ, SEND.

  // Case: I am enabled to act.
  // # ENABLE
  // # If all reply using the new src_seq number and lower enabled values,
  // then ACT, DISABLE, SEND.
  // # If one of the replies has an {enabled} value greater than my own,
  // then SEND. Don't do anything else.
  // # If all reply using the new src_seq number and lower or
  // equal enabled values (including equal values),
  // then ENABLE, SEND.
  // # If some message contains new values that disable all of my actions,
  // then DISABLE, SEND.
}

END_NAMESPACE

int main(int argc, char** argv)
{
  using namespace PROTOCON_NAMESPACE;
  int argi = init_sysCx (&argc, &argv);

  if (argi == argc) {
    Test("");
  }
  else {
    while (argi < argc) {
      Test(argv[argi++]);
    }
  }

  lose_sysCx ();
  return 0;
}

