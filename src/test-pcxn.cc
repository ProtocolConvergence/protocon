
extern "C" {
#include "cx/def.h"
}

#include "test-pcxn.hh"

#include "prot-xfile.hh"
#include "xnsys.hh"

#include "cx/fileb.hh"

#include "namespace.hh"

  void
TestPcXn_rwr()
{
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;

  Xn::VblSymm& vbl_symm = *topo.add_variables("x", 3, 3);

  topo.commit_variables();

  Xn::PcSymm& pc_symm = *topo.add_processes("P", "i", 1);

  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 0, Xn::ReadAccess);
  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 1, Xn::WriteAccess);
  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 2, Xn::ReadAccess);

  sys.commit_initialization();

  PFmlaVbl x_j = topo.pfmla_vbl(*vbl_symm.membs[0]);
  PFmlaVbl x_i = topo.pfmla_vbl(*vbl_symm.membs[1]);
  PFmlaVbl x_k = topo.pfmla_vbl(*vbl_symm.membs[2]);

  for (uint actid = 0; actid < topo.n_possible_acts; ++actid) {
    Xn::ActSymm act;
    topo.action(act, actid);
    const uint a = act.guard(0), b = act.guard(1), c = act.guard(2), d = act.assign(0);
    const X::Fmla result_xn = topo.action_pfmla(actid);
    const X::Fmla expect_xn
      =  P::Fmla(b != d)
      && x_j.identity(a)
      && x_k.identity(c)
      && x_i.transition(b, d);
    Claim( result_xn.equiv_ck(expect_xn) );
  }
}

  void
TestPcXn_ryr()
{
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;

  Xn::VblSymm& vbl_symm = *topo.add_variables("x", 3, 3);

  topo.commit_variables();

  Xn::PcSymm& pc_symm = *topo.add_processes("P", "i", 1);

  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 0, Xn::ReadAccess);
  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 1, Xn::YieldAccess);
  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 2, Xn::ReadAccess);

  sys.commit_initialization();

  PFmlaVbl x_j = topo.pfmla_vbl(*vbl_symm.membs[0]);
  PFmlaVbl x_i = topo.pfmla_vbl(*vbl_symm.membs[1]);
  PFmlaVbl x_k = topo.pfmla_vbl(*vbl_symm.membs[2]);

  for (uint actid = 0; actid < topo.n_possible_acts; ++actid) {
    Xn::ActSymm act;
    topo.action(act, actid);
    const uint a = act.guard(0), b = act.assign(0), c = act.guard(2);
    const X::Fmla result_xn = topo.action_pfmla(actid);
    const X::Fmla expect_xn
      =  x_j.identity(a)
      && x_k.identity(c)
      && x_i != b && x_i.img_eq(b);
    Claim( result_xn.equiv_ck(expect_xn) );
  }
}

static
  X::Fmla
xfmla_rryy(const Xn::Net& topo, uint a, uint b, uint c, uint d)
{
#define V(j)  topo.pfv(0,0,j)
  return
    (V(0).identity(a) && V(1).identity(b)
     && (V(2) != c || V(3) != d)
     && V(2).img_eq(c) && V(3).img_eq(d));
#undef V
}

  void
TestPcXn_rryy()
{
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;

  Xn::VblSymm& x_symm = *topo.add_variables("x", 1, 2);
  Xn::VblSymm& c_symm = *topo.add_variables("c", 2, 2);
  Xn::VblSymm& y_symm = *topo.add_variables("y", 1, 2);

  topo.commit_variables();

  Xn::PcSymm& pc_symm = *topo.add_processes("P", "i", 1);

  topo.add_access(&pc_symm, &x_symm, Xn::NatMap() = 0, Xn::ReadAccess);
  topo.add_access(&pc_symm, &c_symm, Xn::NatMap() = 0, Xn::ReadAccess);
  topo.add_access(&pc_symm, &y_symm, Xn::NatMap() = 0, Xn::YieldAccess);
  topo.add_access(&pc_symm, &c_symm, Xn::NatMap() = 1, Xn::YieldAccess);

  sys.commit_initialization();

  for (uint actid = 0; actid < topo.n_possible_acts; ++actid) {
    const Xn::ActSymm& act = topo.act_of(actid);
    const X::Fmla result_xn = topo.action_pfmla(actid);
    const X::Fmla expect_xn = xfmla_rryy(topo, act.guard(0), act.guard(1),
                                         act.assign(0), act.assign(1));
    Claim( result_xn.equiv_ck(expect_xn) );
  }
}

  void
TestPcXn_rryy_file()
{
  Xn::Sys sys;
  sys.topology.lightweight = true;
  ProtoconFileOpt infile_opt;
  infile_opt.constant_map["N"] = 1;
#define WL << '\n' <<
  infile_opt.text
    << "variable x[N]   < 2;"
    WL "variable c[N+1] < 2;"
    WL "variable y[N]   < 2;"
    WL "(future & future silent) (true);"
    WL "process P[i < N] {"
    WL "  read: x[i], c[i];"
    WL "  yield: y[i], c[i+1];"
    WL "  action: ( x[i]==0 && c[i]==0 --> y[i]:=0; c[i+1]:=0; );"
    WL "  action: ( x[i]==0 && c[i]==1 --> y[i]:=1; c[i+1]:=0; );"
    WL "  action: ( x[i]==1 && c[i]==0 --> y[i]:=1; c[i+1]:=0; );"
    WL "  action: ( x[i]==1 && c[i]==1 --> y[i]:=0; c[i+1]:=1; );"
    WL "}";
#undef WL

  if (!ReadProtoconFile(sys, infile_opt)) {
    Claim( 0 && "Can't parse file" );
  }

  const Xn::Pc& pc = sys.topology.pcs[0];
  const X::Fmla& result_xn = (pc.puppet_xn & pc.global_mask_xn);
  const X::Fmla& expect_xn
    = xfmla_rryy(sys.topology, 0, 0, 0, 0)
    | xfmla_rryy(sys.topology, 0, 1, 1, 0)
    | xfmla_rryy(sys.topology, 1, 0, 1, 0)
    | xfmla_rryy(sys.topology, 1, 1, 0, 1)
    ;
  Claim( result_xn.equiv_ck(expect_xn) );
  Claim2_uint( sys.actions.size() ,==, 4 );
}

static
  X::Fmla
xfmla_ryyr(const Xn::Net& topo, uint a, uint b, uint c, uint d)
{
#define V(j)  topo.pfv(0,0,j)
  return
    (V(0).identity(a) && V(3).identity(d)
     && (V(1) != b || V(2) != c)
     && V(1).img_eq(b) && V(2).img_eq(c));
#undef V
}

  void
TestPcXn_ryyr()
{
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;

  Xn::VblSymm& vbl_symm = *topo.add_variables("x", 4, 3);

  topo.commit_variables();

  Xn::PcSymm& pc_symm = *topo.add_processes("P", "i", 1);

  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 0, Xn::ReadAccess);
  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 1, Xn::YieldAccess);
  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 2, Xn::YieldAccess);
  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 3, Xn::ReadAccess);

  sys.commit_initialization();

  for (uint actid = 0; actid < topo.n_possible_acts; ++actid) {
    const Xn::ActSymm& act = topo.act_of(actid);
    const X::Fmla result_xn = topo.action_pfmla(actid);
    const X::Fmla expect_xn = xfmla_ryyr(topo, act.guard(0), act.assign(0),
                                         act.assign(1), act.guard(3));
    Claim( result_xn.equiv_ck(expect_xn) );
  }
}

static
  X::Fmla
xfmla_yryr(const Xn::Net& topo, uint a, uint b, uint c, uint d)
{
#define V(j)  topo.pfv(0,0,j)
  return
    (V(1).identity(b) && V(3).identity(d)
     && (V(0) != a || V(2) != c)
     && V(0).img_eq(a) && V(2).img_eq(c));
#undef V
}

  void
TestPcXn_yryr_dizzy()
{
  const bool IgnoreCache = false;
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;
  topo.lightweight = IgnoreCache;

  Xn::VblSymm& vbl_symm = *topo.add_variables("x", 4, 3);

  topo.commit_variables();

  Xn::PcSymm& pc_symm = *topo.add_processes("P", "i", 1);

  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 1, Xn::YieldAccess);
  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 0, Xn::ReadAccess);
  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 2, Xn::YieldAccess);
  topo.add_access(&pc_symm, &vbl_symm, Xn::NatMap() = 3, Xn::ReadAccess);

  {
    Xn::LinkSymmetry link_symmetry(2);
    link_symmetry.add_link_symmetry(Table<uint>() << 0 << 2, "");
    link_symmetry.add_link_symmetry(Table<uint>() << 1 << 3, "");
    pc_symm.spec->link_symmetries.push(link_symmetry);
  }

  sys.commit_initialization();

  for (uint actid = 0; actid < topo.n_possible_acts; ++actid) {
    if (actid != topo.representative_action_index(actid))
      continue;

    const Xn::ActSymm& act = topo.act_of(actid);
    X::Fmla result_xn;
    if (IgnoreCache) {
      X::Fmlae result_xfmlae = topo.action_xfmlae(actid);
      result_xfmlae.self_disable();
      result_xn = result_xfmlae.xfmla();
    }
    else {
      result_xn = topo.action_pfmla(actid);
    }
    //                       x'_ij          x_ji          x'_ik          x_ki
    X::Fmla expect_xn
      = xfmla_yryr(topo, act.assign(0), act.guard(1), act.assign(1), act.guard(3))
      | xfmla_yryr(topo, act.assign(1), act.guard(3), act.assign(0), act.guard(1))
      ;
    expect_xn -= expect_xn.img();

    Claim( result_xn.equiv_ck(expect_xn) );
  }
}

  void
TestPcXn_yerrerr_dizzy()
{
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;

  Xn::VblSymm& b_symm = *topo.add_variables("b", 3, 2);
  Xn::VblSymm& w_symm = *topo.add_variables("w", 4, 2);

  topo.commit_variables();

  Xn::PcSymm& pc_symm = *topo.add_processes("P", "i", 1);

  topo.add_access(&pc_symm, &b_symm, Xn::NatMap() = 1, Xn::YieldAccess);
  topo.add_access(&pc_symm, &w_symm, Xn::NatMap() = 1, Xn::EffectAccess);
  topo.add_access(&pc_symm, &b_symm, Xn::NatMap() = 0, Xn::ReadAccess);
  topo.add_access(&pc_symm, &w_symm, Xn::NatMap() = 0, Xn::ReadAccess);
  topo.add_access(&pc_symm, &w_symm, Xn::NatMap() = 2, Xn::EffectAccess);
  topo.add_access(&pc_symm, &b_symm, Xn::NatMap() = 2, Xn::ReadAccess);
  topo.add_access(&pc_symm, &w_symm, Xn::NatMap() = 3, Xn::ReadAccess);

  {
    Xn::LinkSymmetry link_symmetry(2);
    link_symmetry.add_link_symmetry(Table<uint>() << 1 << 4, "");
    link_symmetry.add_link_symmetry(Table<uint>() << 2 << 5, "");
    link_symmetry.add_link_symmetry(Table<uint>() << 3 << 6, "");
    pc_symm.spec->link_symmetries.push(link_symmetry);
  }

  sys.commit_initialization();

  PFmlaVbl w_ji = topo.pfmla_vbl(*w_symm.membs[0]);
  PFmlaVbl w_ij = topo.pfmla_vbl(*w_symm.membs[1]);
  PFmlaVbl w_ik = topo.pfmla_vbl(*w_symm.membs[2]);
  PFmlaVbl w_ki = topo.pfmla_vbl(*w_symm.membs[3]);
  PFmlaVbl b_j = topo.pfmla_vbl(*b_symm.membs[0]);
  PFmlaVbl b_i = topo.pfmla_vbl(*b_symm.membs[1]);
  PFmlaVbl b_k = topo.pfmla_vbl(*b_symm.membs[2]);

  for (uint actid = 0; actid < topo.n_possible_acts; ++actid) {
    if (actid != topo.representative_action_index(actid))
      continue;

    Xn::ActSymm act;
    topo.action(act, actid);
    OPut(std::cerr, act);
    std::cerr << std::endl;

    const uint s_i = act.assign(0), s_ij = act.assign(1), s_ik = act.assign(2);
    const uint s_j = act.guard(2), s_k = act.guard(5);
    const uint s_ji = act.guard(3), s_ki = act.guard(6);

    if ((s_ij < 2 && s_ik == 2) || (s_ij == 2 && s_ik < 2))
      continue;

    X::Fmla result_xn = topo.action_pfmla(actid);
    X::Fmla expect_xn =
      (b_j.identity(s_j) && b_k.identity(s_k)
       && w_ji.identity(s_ji) && w_ki.identity(s_ki)
       && (b_i != s_i
           || (s_ij < 2 ? w_ij != s_ij : P::Fmla(false))
           || (s_ik < 2 ? w_ik != s_ik : P::Fmla(false)))
       && b_i.img_eq(s_i)
       && (s_ij < 2 ? w_ij.img_eq(s_ij) : w_ij.identity())
       && (s_ik < 2 ? w_ik.img_eq(s_ik) : w_ik.identity()))
      ||
      (b_j.identity(s_k) && b_k.identity(s_j)
       && w_ji.identity(s_ki) && w_ki.identity(s_ji)
       && (b_i != s_i
           || (s_ik < 2 ? w_ij != s_ik : P::Fmla(false))
           || (s_ij < 2 ? w_ik != s_ij : P::Fmla(false)))
       && b_i.img_eq(s_i)
       && (s_ik < 2 ? w_ij.img_eq(s_ik) : w_ij.identity())
       && (s_ij < 2 ? w_ik.img_eq(s_ij) : w_ik.identity()));
    expect_xn -= expect_xn.img();

    Claim( result_xn.equiv_ck(expect_xn) );
  }
}

/** Topology of unidirectional ring coloring that uses a random write.**/
  void
TestPcXn_rw_random()
{
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;

  Xn::VblSymm& x_symm = *topo.add_variables("c", 2, 3);

  topo.commit_variables();

  Xn::PcSymm& pc_symm = *topo.add_processes("P", "i", 1);

  topo.add_access(&pc_symm, &x_symm, Xn::NatMap() = 0, Xn::ReadAccess);
  topo.add_access(&pc_symm, &x_symm, Xn::NatMap() = 1, Xn::RandomWriteAccess);

  sys.commit_initialization();

  PFmlaVbl x_j = topo.pfmla_vbl(*x_symm.membs[0]);
  PFmlaVbl x_i = topo.pfmla_vbl(*x_symm.membs[1]);

  for (uint actid = 0; actid < topo.n_possible_acts; ++actid) {
    if (actid != topo.representative_action_index(actid))
      continue;

    Xn::ActSymm act;
    topo.action(act, actid);

    // Values used in the guard.
    const uint s_j = act.guard(0);
    const uint s_i = act.guard(1);

    const X::Fmla result_xn = topo.action_pfmla(actid);
    const X::Fmla expect_xn = (x_j.identity(s_j) && x_i == s_i);

    Claim( result_xn.equiv_ck(expect_xn) );
  }
}

END_NAMESPACE
