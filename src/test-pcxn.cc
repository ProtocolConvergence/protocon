
extern "C" {
#include "cx/syscx.h"
}

#include "cx/synhax.hh"
#include "xnsys.hh"

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

  PFmlaVbl x_ji = topo.pfmla_vbl(*vbl_symm.membs[0]);
  PFmlaVbl x_ij = topo.pfmla_vbl(*vbl_symm.membs[1]);
  PFmlaVbl x_ik = topo.pfmla_vbl(*vbl_symm.membs[2]);
  PFmlaVbl x_ki = topo.pfmla_vbl(*vbl_symm.membs[3]);

  for (uint actid = 0; actid < topo.n_possible_acts; ++actid) {
    Xn::ActSymm act;
    topo.action(act, actid);
    const uint a = act.guard(0), b = act.assign(0), c = act.assign(1), d = act.guard(3);
    const X::Fmla result_xn = topo.action_pfmla(actid);
    const X::Fmla expect_xn
      =  x_ji.identity(a)
      && x_ki.identity(d)
      && (x_ij != b || x_ik != c)
      && x_ij.img_eq(b) && x_ik.img_eq(c);
    Claim( result_xn.equiv_ck(expect_xn) );
  }
}

  void
TestPcXn_yryr_dizzy()
{
  Xn::Sys sys;
  Xn::Net& topo = sys.topology;

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

  PFmlaVbl x_ji = topo.pfmla_vbl(*vbl_symm.membs[0]);
  PFmlaVbl x_ij = topo.pfmla_vbl(*vbl_symm.membs[1]);
  PFmlaVbl x_ik = topo.pfmla_vbl(*vbl_symm.membs[2]);
  PFmlaVbl x_ki = topo.pfmla_vbl(*vbl_symm.membs[3]);

  for (uint actid = 0; actid < topo.n_possible_acts; ++actid) {
    if (actid != topo.representative_action_index(actid))
      continue;

    Xn::ActSymm act;
    topo.action(act, actid);
    const uint a = act.guard(1), b = act.assign(0), c = act.assign(1), d = act.guard(3);
    const X::Fmla result_xn = topo.action_pfmla(actid);
    const X::Fmla expect_xn =
      (x_ji.identity(a) && x_ki.identity(d)
       && (x_ij != b || x_ik != c)
       && x_ij.img_eq(b) && x_ik.img_eq(c))
      ||
      (x_ji.identity(d) && x_ki.identity(a)
       && (x_ij != c || x_ik != b)
       && x_ij.img_eq(c) && x_ik.img_eq(b));

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
    OFile ofile( stderr_OFile () );
    OPut(ofile, act);
    ofile << ofile.endl();

    const uint s_i = act.assign(0), s_ij = act.assign(1), s_ik = act.assign(2);
    const uint s_j = act.guard(2), s_k = act.guard(5);
    const uint s_ji = act.guard(3), s_ki = act.guard(6);

    if ((s_ij < 2 && s_ik == 2) || (s_ij == 2 && s_ik < 2))
      continue;

    const X::Fmla result_xn = topo.action_pfmla(actid);
    const X::Fmla expect_xn =
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

    Claim( result_xn.subseteq_ck(expect_xn) );
    Claim( expect_xn.subseteq_ck(result_xn) );
    Claim( result_xn.equiv_ck(expect_xn) );
  }
}

END_NAMESPACE

