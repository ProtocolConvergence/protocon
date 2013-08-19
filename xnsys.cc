
#include "xnsys.hh"

namespace Xn {

/**
 * Commit to the topology represented by the vector of processes.
 *
 * TODO this function needs to go away,
 * or at least we need to initialize on a per-process basis.
 *
 * 1. Find /nPossibleActs/ for each process.
 */
  void
Net::commit_initialization()
{
  uint ntotal = 0;
  for (uint i = 0; i < pc_symms.sz(); ++i) {
    Xn::PcSymm& pc = pc_symms[i];
    pc.act_idx_offset = ntotal;
    pc.pre_dom_offset = total_pre_domsz;

    pc.pre_domsz = 1;
    for (uint j = 0; j < pc.rvbl_symms.sz(); ++j) {
      uint domsz = pc.rvbl_symms[j]->domsz;
      pc.doms.push(domsz);
      pc.pre_domsz *= domsz;
    }

    pc.img_domsz = 1;
    for (uint j = 0; j < pc.wvbl_symms.sz(); ++j) {
      uint domsz = pc.wvbl_symms[j]->domsz;
      pc.doms.push(domsz);
      pc.img_domsz *= domsz;
    }

    total_pre_domsz += pc.pre_domsz;
    pc.n_possible_acts = (pc.pre_domsz * pc.img_domsz);
    ntotal += pc.n_possible_acts;
  }

  act_pfmlas.resize(ntotal);
  n_possible_acts = ntotal;
  for (uint i = 0; i < ntotal; ++i) {
    this->make_action_pfmla(i);
  }
}

  VblSymm*
Net::add_variables(const String& name, uint nmembs, uint domsz,
                   Vbl::ShadowPuppetRole role)
{
  VblSymm& symm = vbl_symms.grow1();
  symm.name = name;
  symm.domsz = domsz;
  symm.pfmla_list_id = pfmla_ctx.add_vbl_list();
  symm.shadow_puppet_role = role;

  for (uint i = 0; i < nmembs; ++i) {
    Vbl* vbl = &vbls.push(Vbl(&symm, i));
    symm.membs.push(vbl);
    vbl->pfmla_idx = pfmla_ctx.add_vbl(name_of (*vbl), domsz);
    pfmla_ctx.add_to_vbl_list(symm.pfmla_list_id, vbl->pfmla_idx);

    const Cx::PFmlaVbl& pf_vbl = this->pfmla_vbl(*vbl);
    this->identity_pfmla &= pf_vbl.img_eq(pf_vbl);
  }
  return &symm;
}

  PcSymm*
Net::add_processes(const String& name, uint nmembs)
{
  PcSymm& symm = pc_symms.grow1();
  symm.name = name;
  for (uint i = 0; i < nmembs; ++i) {
    Pc& pc = pcs.push(Pc(&symm, i));
    symm.membs.push(&pc);
    pc.act_unchanged_pfmla = this->identity_pfmla;
  }
  return &symm;
}

  void
Net::add_read_access (PcSymm* pc_symm, const VblSymm* vbl_symm,
                      const NatMap& indices)
{
  pc_symm->rvbl_symms.push(vbl_symm);
  pc_symm->write_flags.push_back(false);
  pc_symm->rindices.push(indices);
  for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
    const Vbl* vbl = vbl_symm->membs[indices.index(i, vbl_symm->membs.sz())];
    pc_symm->membs[i]->rvbls.push(vbl);
  }
}

  void
Net::add_write_access (PcSymm* pc_symm, const VblSymm* vbl_symm,
                       const NatMap& indices)
{
  add_read_access (pc_symm, vbl_symm, indices);
  pc_symm->wvbl_symms.push(vbl_symm);
  pc_symm->wmap.push(pc_symm->rvbl_symms.sz() - 1);
  pc_symm->write_flags[pc_symm->rvbl_symms.sz() - 1] = true;
  pc_symm->windices.push(indices);
  for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
    const Vbl* vbl = vbl_symm->membs[indices.index(i, vbl_symm->membs.sz())];
    Pc& pc = *pc_symm->membs[i];
    pc.wvbls.push(vbl);
    pc.act_unchanged_pfmla =
      pc.act_unchanged_pfmla.smooth(pfmla_vbl(*vbl));
  }
}

  uint
Net::action_pcsymm_index(uint actidx) const
{
  for (uint i = 0; i < pc_symms.sz()-1; ++i) {
    if (actidx < pc_symms[i+1].act_idx_offset) {
      return i;
    }
  }
  return pc_symms.sz() - 1;
}

static
  void
swap_pre_img (uint* vals, const Xn::PcSymm& pc_symm)
{
  uint off = pc_symm.rvbl_symms.sz();
  for (uint i = 0; i < pc_symm.wmap.sz(); ++i) {
    uint* pre_x = &vals[pc_symm.wmap[i]];
    uint* img_x = &vals[off + i];
    uint tmp = *img_x;
    *img_x = *pre_x;
    *pre_x = tmp;
  }
}

  void
PcSymm::action(ActSymm& act, uint actidx) const
{
  act.pc_symm = this;
  const Xn::PcSymm& pc = *this;

  act.pre_idx = actidx / pc.img_domsz;
  act.img_idx = actidx % pc.img_domsz;

  act.vals.resize(pc.rvbl_symms.sz() + pc.wvbl_symms.sz());
  Cx::state_of_index (&act.vals[0], actidx, pc.doms);

  swap_pre_img (&act.vals[0], pc);
  act.pre_idx_of_img =
    index_of_state (&act.vals[0], &pc.doms[0], pc.rvbl_symms.sz());
  swap_pre_img (&act.vals[0], pc);
}

  void
Net::action(ActSymm& act, uint actidx) const
{
  const Xn::PcSymm& pc =
    this->pc_symms[this->action_pcsymm_index(actidx)];
  pc.action(act, actidx - pc.act_idx_offset);
}

  uint
Net::action_index(const Xn::ActSymm& act) const
{
  const Xn::PcSymm& pc = *act.pc_symm;
  return pc.act_idx_offset +
    Cx::index_of_state (&act.vals[0], pc.doms);

}

  uint
Net::action_pre_index(uint actidx) const
{
  uint pcidx = this->action_pcsymm_index(actidx);
  const Xn::PcSymm& pc_symm = pc_symms[pcidx];
  actidx -= pc_symm.act_idx_offset;
  actidx /= pc_symm.img_domsz;
  return actidx + pc_symm.pre_dom_offset;
}

  uint
Net::action_img_index(uint actidx) const
{
  uint pcidx = this->action_pcsymm_index(actidx);
  const Xn::PcSymm& pc_symm = pc_symms[pcidx];
  actidx -= pc_symm.act_idx_offset;
  return actidx % pc_symm.img_domsz;
}

  ostream&
Net::oput(ostream& of,
          const Cx::PFmla& pf,
          const String& pfx,
          const String& sfx) const
{

  (void) pf;
  of << pfx << "/*(NOT IMPLEMENTED)*/" << sfx;
  /*
  return this->pfCtx.oput(of, pf, this->vVblList, pfx, sfx);
  */
  return of;
}

  Cx::OFile&
Net::oput_pfmla(Cx::OFile& of, Cx::PFmla pf,
                Sign pre_or_img, bool just_one) const
{
  Cx::Table<uint> state_pre(this->vbls.sz(), 0);
  Cx::Table<uint> state_img(this->vbls.sz(), 0);
  while (!pf.tautology_ck(false))
  {
    Cx::PFmla pf_pre = pf.pick_pre();
    Cx::PFmla pf_img = pf.img(pf_pre).pick_pre();

    for (uint i = 0; i < this->vbls.sz(); ++i) {
      state_pre[i] = this->vbls[i].pfmla_idx;
      state_img[i] = this->vbls[i].pfmla_idx;
    }
    pf_pre.state(&state_pre[0], state_pre);
    pf_img.state(&state_img[0], state_img);

    if (pre_or_img <= 0) {
      of << "pre:";
      for (uint i = 0; i < this->vbls.sz(); ++i) {
        of << ' ' << state_pre[i];
      }
      of << '\n';
    }
    if (pre_or_img >= 0) {
      of << "img:";
      for (uint i = 0; i < this->vbls.sz(); ++i) {
        of << ' ' << state_img[i];
      }
      of << '\n';
    }

    if (just_one)  break;

    if (pre_or_img < 0)
      pf -= pf_pre;
    else if (pre_or_img > 0)
      pf -= pf_img.as_img();
    else
      pf -= pf_pre & pf_img.as_img();
  }
  return of;
}


  Cx::OFile&
Net::oput_one_xn(Cx::OFile& of, const Cx::PFmla& pf) const
{
  return this->oput_pfmla(of, pf, 0, true);
}

  Cx::OFile&
Net::oput_all_xn(Cx::OFile& of, const Cx::PFmla& pf) const
{
  return this->oput_pfmla(of, pf, 0, false);
}

  Cx::OFile&
Net::oput_all_pf(Cx::OFile& of, const Cx::PFmla& pf) const
{
  return this->oput_pfmla(of, pf, -1, false);
}


  void
Sys::commit_initialization()
{
  Xn::Net& topo = this->topology;
  topo.commit_initialization();

  this->shadow_self = true;

  for (uint i = 0; i < topo.vbls.sz(); ++i) {
    const Xn::Vbl& vbl = topo.vbls[i];
    if (vbl.symm->pure_shadow_ck()) {
      shadow_puppet_synthesis = true;
    }
    if (vbl.symm->pure_puppet_ck()) {
      shadow_puppet_synthesis = true;
      pure_puppet_vbl_exists = true;
      topo.pfmla_ctx.add_to_vbl_list (pure_puppet_pfmla_list_id, vbl.pfmla_idx);
    }
    if (vbl.symm->shadow_ck()) {
      topo.pfmla_ctx.add_to_vbl_list (shadow_pfmla_list_id, vbl.pfmla_idx);
      const Cx::PFmlaVbl& x = topo.pfmla_ctx.vbl(vbl.pfmla_idx);
      shadow_self &= (x.img_eq(x));
    }
    if (vbl.symm->puppet_ck()) {
      puppet_vbl_exists = true;
      topo.pfmla_ctx.add_to_vbl_list (puppet_pfmla_list_id, vbl.pfmla_idx);
    }
  }

  for (uint act_idx = 0; act_idx < topo.n_possible_acts; ++act_idx) {
    const Cx::PFmla& act_pfmla = topo.action_pfmla(act_idx);
    if (act_pfmla <= this->direct_pfmla) {
      this->actions.push_back(act_idx);
    }
    else {
      Claim( !act_pfmla.overlap_ck(this->direct_pfmla) );
    }
  }
}

  bool
Sys::integrityCk() const
{
  bool good = true;
  const Net& topo = this->topology;

  if (this->invariant.tautology_ck(false)) {
    DBog0( "Error: Invariant is empty!" );
    good = false;
  }

  if (!this->invariant.smooth(this->shadow_pfmla_list_id).tautology_ck(true)) {
    DBog0( "Error: Invariant includes non-shadow variables." );
    good = false;
  }

  if (!(this->shadow_pfmla.img(this->invariant) <= this->invariant)) {
    DBog0( "Error: Protocol is not closed in the invariant!" );
    good = false;

    Cx::PFmla bad_xn = this->shadow_pfmla & this->invariant & (~this->invariant).as_img();
    Cx::OFile of( stderr_OFile () );
    topo.oput_one_xn(of, bad_xn);
  }

  return good;
}

}

  Cx::OFile&
OPut(Cx::OFile& of, const Xn::ActSymm& act)
{
  const Xn::PcSymm& pc = *act.pc_symm;
  of << "/*" << pc.name << "[i]" << "*/ ";
  for (uint i = 0; i < pc.rvbl_symms.sz(); ++i) {
    if (i != 0)  of << " && ";
    of << pc.rvbl_symms[i]->name
      << "[" << pc.rindices[i].expression("i") << "]"
      << "==" << act.guard(i);
  }
  of << " -->";
  for (uint i = 0; i < pc.wvbl_symms.sz(); ++i) {
    of << ' ' << pc.wvbl_symms[i]->name
      << "[" << pc.windices[i].expression("i") << "]"
      << ":=" << act.assign(i) << ';';
  }
  return of;
}

  PF
LegitInvariant(const Xn::Sys& sys, const PF& lo_xn_rel, const PF& hi_xn_rel)
{
  if (!sys.shadow_puppet_synthesis_ck())  return sys.invariant;

  const Cx::PFmla& shadow_invariant = sys.invariant;
  const Cx::PFmla& shadow_protocol = sys.shadow_pfmla;
  const Cx::PFmla& shadow_self = sys.shadow_self;
  const Cx::PFmla& shadow_live = shadow_invariant & shadow_protocol;

  // There shouldn't be non-progress cycles.
  if (CycleCk(lo_xn_rel & shadow_self & shadow_protocol.pre(), shadow_invariant)) {
    return PF(false);
  }

  // Invariant states with no transitions to them.
  const Cx::PFmla& shadow_beg =
    shadow_invariant - shadow_protocol.img(shadow_invariant);
  // Invariant states with no transitions from them.
  const Cx::PFmla& shadow_end =
    shadow_invariant - shadow_protocol.pre(shadow_invariant);

  // Over-approximation of invariant.
  Cx::PFmla hi_invariant = shadow_invariant;
  // Over-approximation of protocol which does not change shadow variables.
  Cx::PFmla hi_self = hi_xn_rel & shadow_self;
  // Over-approximation of protocol which does change shadow variables.
  Cx::PFmla hi_live = hi_xn_rel & shadow_protocol;

  // Trim all states which cannot be in the invariant since we cannot
  // simulate the shadow protocol in those states given the current
  // over-approximated protocol.
  while (true)
  {
    hi_invariant = ClosedSubset(lo_xn_rel, hi_invariant);

    const Cx::PFmla old_invariant = hi_invariant;
    const Cx::PFmla& hi_img = hi_invariant.as_img();

    hi_self &= hi_invariant;         
    hi_self &= hi_img;

    hi_live &= hi_invariant;
    hi_live &= hi_img;
    hi_live -= (shadow_live - sys.smooth_pure_puppet_img_vbls(hi_live)).pre();

    const Cx::PFmla& hi_beg = hi_invariant & shadow_beg;
    const Cx::PFmla& hi_end = hi_invariant & shadow_end;

    hi_invariant &= ForwardReachability (hi_self, hi_beg | hi_live.img());
    hi_invariant &= BackwardReachability(hi_self, hi_end | hi_live.pre());

    //hi_invariant &= shadow_beg | hi_protocol.img(hi_invariant);
    //hi_invariant &= shadow_end | hi_protocol.pre(hi_invariant);

    if (old_invariant.equiv_ck(hi_invariant)) {
      break;
    }
  }

  if (!shadow_invariant.equiv_ck(sys.smooth_pure_puppet_vbls(hi_invariant))) {
    return PF(false);
  }

  //if (CycleCk(lo_xn_rel, ~hi_invariant)) {
  if (CycleCk(lo_xn_rel, shadow_invariant - hi_invariant)) {
    return PF(false);
  }

#if 0
  Cx::PFmla shadow_live = shadow_protocol & shadow_invariant;
  Cx::PFmla hi_live = hi_protocol & hi_invariant & hi_invariant.as_img();

  while (!shadow_live.tautology_ck(false))
  {
    bool found = false;

    Cx::PFmla shadow_seed = shadow_live.pick_pre();
    Cx::PFmla shadow_reach = UndirectedReachability(shadow_live, shadow_seed);
    shadow_live -= shadow_reach;

    Cx::PFmla hi_reach_set = hi_invariant & shadow_reach;

    while (!hi_reach_set.tautology_ck(false))
    {
      Cx::PFmla hi_seed = hi_reach_set & shadow_reach;
      Cx::PFmla hi_reach = UndirectedReachability(hi_live, hi_seed);

      hi_reach_set -= hi_reach;

      if (shadow_reach.equiv_ck(sys.smooth_pure_puppet_vbls(hi_reach))) {
        found = true;
      }
      else {
        hi_invariant -= hi_reach;
      }
    }

    if (!found) {
      return Cx::PFmla(false);
    }
  }
#endif

  const Cx::PFmla& lhs =
    sys.smooth_pure_puppet_vbls(shadow_live);
  const Cx::PFmla& rhs =
    sys.smooth_pure_puppet_vbls(hi_live);

#if 0
  Claim( lhs.equiv_ck(rhs) );
#else
  if (!lhs.equiv_ck(rhs)) {
#if 0
    if (!(lhs <= rhs)) {
      DBog0("shadow_protocol is bigger");
      sys.topology.oput_one_xn(std::cerr, lhs - rhs);
    }
    if (!(rhs <= lhs)) {
      DBog0("hi_protocol is bigger");
      sys.topology.oput_one_xn(std::cerr, rhs - lhs);
    }
#endif
    return PF(false);
  }
#endif
  return hi_invariant;
}

/**
 * Check for weak convergence to the invariant.
 */
  bool
WeakConvergenceCk(const Xn::Sys& sys, const PF& xnRel, const PF& invariant)
{
  //if (sys.shadow_puppet_synthesis_ck()) {
  //  const PF& shadow_pfmla =
  //    sys.smooth_pure_puppet_vbls(xnRel & invariant & invariant.as_img())
  //    - sys.shadow_self;
  //  if (!shadow_pfmla.equiv_ck(sys.shadow_pfmla & sys.invariant)) {
  //    return false;
  //  }
  //}

  PF span0( invariant );
  while (!span0.tautology_ck(true)) {
    const Cx::PFmla& span1 = span0 | xnRel.pre(span0);
    if (span1.equiv_ck(span0))  return false;
    span0 = span1;
  }
  return true;
}

  bool
WeakConvergenceCk(const Xn::Sys& sys, const PF& xnRel)
{
  return WeakConvergenceCk(sys, xnRel, sys.invariant);
}

/**
 * Create a persistent PF for this action.
 * \sa commit_initialization()
 **/
  void
Xn::Net::make_action_pfmla(uint actidx)
{
  Xn::ActSymm act;
  this->action(act, actidx);
  const Xn::PcSymm& pc_symm = *act.pc_symm;

  Cx::PFmla pf(false);

  for (uint i = 0; i < pc_symm.membs.sz(); ++i) {
    const Xn::Pc& pc = *pc_symm.membs[i];
    Cx::PFmla actpf(true);

    for (uint j = 0; j < pc.rvbls.sz(); ++j) {
      const Cx::PFmlaVbl& vbl = pfmla_vbl(*pc.rvbls[j]);
      actpf &= (vbl == act.guard(j));
    }
    for (uint j = 0; j < pc.wvbls.sz(); ++j) {
      const Cx::PFmlaVbl& vbl = pfmla_vbl(*pc.wvbls[j]);
      actpf &= (vbl.img_eq(act.assign(j)));
    }
    pf |= (pc.act_unchanged_pfmla & actpf);
  }

  act_pfmlas[actidx] = pf;
}

