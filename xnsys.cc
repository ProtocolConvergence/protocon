
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
    uint n = 1;
    pc.act_idx_offset = ntotal;

    for (uint j = 0; j < pc.rvbl_symms.sz(); ++j) {
      uint domsz = pc.rvbl_symms[j]->domsz;
      pc.doms.push(domsz);
      n *= domsz;
    }
    for (uint j = 0; j < pc.wvbl_symms.sz(); ++j) {
      uint domsz = pc.wvbl_symms[j]->domsz;
      pc.doms.push(domsz);
      n *= domsz;
    }

    pc.n_possible_acts = n;
    ntotal += n;
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

  void
Net::action(ActSymm& act, uint actidx) const
{
  uint pcidx = this->action_pcsymm_index(actidx);
  act.pc_symm = &pc_symms[pcidx];
  const Xn::PcSymm& pc = *act.pc_symm;

  actidx -= pc.act_idx_offset;

  act.vals.resize(pc.rvbl_symms.sz() + pc.wvbl_symms.sz());
  Cx::state_of_index (&act.vals[0], actidx, pc.doms);

}

  uint
Net::action_index(const Xn::ActSymm& act) const
{
  const Xn::PcSymm& pc = *act.pc_symm;
  return pc.act_idx_offset +
    Cx::index_of_state (&act.vals[0], pc.doms);

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
  }

  return good;
}

}

  ostream&
OPut(ostream& of, const Xn::ActSymm& act)
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
LegitInvariant(const Xn::Sys& sys, const PF& loXnRel, const PF& hiXnRel)
{
  if (!sys.shadow_puppet_synthesis_ck())  return sys.invariant;

  const PF& smooth_self = sys.shadow_self;

  const PF& smooth_live = sys.invariant;
  const PF& smooth_protocol = sys.shadow_pfmla;

  PF puppet_live = smooth_live - (loXnRel - smooth_protocol - smooth_self).pre();
  puppet_live = ClosedSubset(loXnRel, puppet_live);
  const PF& puppet_protocol = hiXnRel & (smooth_protocol | smooth_self);

  if (CycleCk(loXnRel & smooth_self, puppet_live)) {
    return PF(false);
  }

  const PF& smooth_beg = smooth_live - smooth_protocol.img(smooth_live);
  const PF& smooth_end = smooth_live - smooth_protocol.pre(smooth_live);

  while (true)
  {
    const PF old_live = puppet_live;

    puppet_live &= (smooth_beg & puppet_live) | puppet_protocol.img(puppet_live);
    puppet_live &= (smooth_end & puppet_live) | puppet_protocol.pre(puppet_live);

    if (old_live.equiv_ck(puppet_live)) {
      break;
    }
  }

  if (!smooth_live.equiv_ck(sys.smooth_pure_puppet_vbls(puppet_live))) {
    return PF(false);
  }

  if (!(smooth_live & smooth_protocol).equiv_ck(sys.smooth_pure_puppet_vbls(puppet_live & (puppet_protocol - smooth_self)))) {
    return PF(false);
  }
  return puppet_live;
}

/**
 * Check for weak convergence to the invariant.
 */
  bool
WeakConvergenceCk(const Xn::Sys& sys, const PF& xnRel, const PF& invariant)
{
  if (sys.shadow_puppet_synthesis_ck()) {
    const PF& shadow_pfmla = sys.smooth_pure_puppet_vbls(xnRel & invariant);
    if (!sys.shadow_pfmla <= shadow_pfmla) {
      return false;
    }
  }

  PF span0( invariant );
  while (!span0.tautology_ck(true)) {
    PF span1( span0 | xnRel.pre(span0) );
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

