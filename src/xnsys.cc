
#include "xnsys.hh"
#include <cx/bittable.hh>
#include <cx/tuple.hh>

Cx::OFile DBogOF( stderr_OFile () );

#include "namespace.hh"
namespace Xn {

/**
 * Commit to the topology represented by the vector of processes.
 *
 * 1. Find /nPossibleActs/ for each process.
 */
  void
Net::commit_initialization()
{
  for (uint i = 0; i < pc_symms.sz(); ++i) {
    const Xn::PcSymm& pc_symm = pc_symms[i];
    for (uint j = 0; j < pc_symm.wvbl_symms.sz(); ++j) {
      if (pc_symm.spec->waccess(j).random_write_ck()) {
        this->random_write_exists = true;
      }
    }
  }

  uint ntotal = 0;
  for (uint i = 0; i < pc_symms.sz(); ++i) {
    Xn::PcSymm& pc = pc_symms[i];
    pc.init_representative();
    pc.act_idx_offset = ntotal;
    pc.pre_dom_offset = total_pre_domsz;

    pc.pre_domsz = 1;
    for (uint j = 0; j < pc.rvbl_symms.sz(); ++j) {
      uint domsz = pc.spec->access[j].rdomsz();
      pc.doms.push(domsz);
      pc.pre_domsz *= domsz;
    }

    pc.img_domsz = 1;
    for (uint j = 0; j < pc.wvbl_symms.sz(); ++j) {
      uint domsz = pc.spec->waccess(j).wdomsz();
      pc.doms.push(domsz);
      pc.img_domsz *= domsz;
    }

    total_pre_domsz += pc.pre_domsz;
    pc.n_possible_acts = (pc.pre_domsz * pc.img_domsz);
    ntotal += pc.n_possible_acts;
  }

  this->n_possible_acts = ntotal;
  if (this->featherweight)
    return;

  // Smooth out the 'random read' variables.
  for (uint vblidx = 0; vblidx < this->vbls.sz(); ++vblidx) {
    const Xn::Vbl& vbl = this->vbls[vblidx];
    if (!vbl.random_ck())
      continue;
    this->random_read_exists = true;

    const PFmlaVbl& pfmla_vbl = this->pfmla_vbl(vbl);
    this->identity_xn = this->identity_xn.smooth(pfmla_vbl);
    this->xfmlae_ctx.identity_xn = this->xfmlae_ctx.identity_xn.smooth(pfmla_vbl);

    for (uint pcidx = 0; pcidx < this->pcs.sz(); ++pcidx) {
      pfmla_ctx.add_to_vbl_list(xfmlae_ctx.wvbl_list_ids[pcidx],
                                id_of(pfmla_vbl));
      this->xfmlae_ctx.global_mask_xns[pcidx] =
        this->xfmlae_ctx.global_mask_xns[pcidx].smooth(pfmla_vbl);
      this->pcs[pcidx].global_mask_xn =
        this->pcs[pcidx].global_mask_xn.smooth(pfmla_vbl);
    }
  }

  represented_actions.resize(ntotal);
  for (uint actidx = 0; actidx < ntotal; ++actidx) {
    uint rep_actidx = representative_action_index(actidx);
    represented_actions[rep_actidx].push(actidx);
  }
  this->fixup_pc_xns();
  if (this->lightweight)
    return;
  Claim2( act_xfmlaes.sz() ,==, 0 );
  act_xfmlaes.affysz(ntotal, X::Fmlae(&this->xfmlae_ctx));
  for (uint i = 0; i < ntotal; ++i) {
    this->cache_action_xfmla(i);
  }
}

  void
Net::fixup_pc_xns()
{
  for (uint pcidx = 0; pcidx < this->pcs.sz(); ++pcidx) {
    Xn::Pc& pc = this->pcs[pcidx];
    const Xn::PcSymm& pc_symm = *pc.symm;

    bool probabilistic = false;
    for (uint i = 0; i < pc.wvbls.sz(); ++i) {
      if (pc_symm.spec->waccess(i).random_write_ck()) {
        probabilistic = true;
        break;
      }
    }
    if (probabilistic) {
      P::Fmla okay_xn( pc.closed_assume );
      const uint wvbl_list_id = xfmlae_ctx.wvbl_list_ids[pcidx];
      okay_xn &= pc.closed_assume.subst_to_img(wvbl_list_id);
      okay_xn &= ~pc.forbid_xn;
      if (pc.permit_xn.sat_ck()) {
        okay_xn &= pc.permit_xn;
      }
      pc.puppet_xn &= okay_xn;
    }
  }
}

  VblSymm*
Net::add_variables(const String& name, uint nmembs, uint domsz,
                   Xn::ShadowPuppetRole role)
{
  // Cannot add variables after committing them.
  Claim2( vbls.sz() ,==, 0 );

  VblSymm& symm = vbl_symms.grow1();
  symm.spec = &spec->vbl_symms.grow1();
  symm.domsz = domsz;
  symm.spec->name = name;
  symm.spec->domsz_expression = domsz;
  symm.spec->nmembs_expression = nmembs;
  symm.spec->domsz = domsz;
  symm.spec->shadow_puppet_role = role;
  symm.pfmla_list_id = pfmla_ctx.add_vbl_list();
  symm.membs.grow(nmembs, 0);

  return &symm;
}

  void
Net::commit_variable(VblSymm& symm, uint i)
{
  Vbl* vbl = &vbls.push(Vbl(&symm, i));
  symm.membs[i] = vbl;

  if (this->featherweight)  return;

  vbl->pfmla_idx = pfmla_ctx.add_vbl(name_of (*vbl), symm.domsz);
  pfmla_ctx.add_to_vbl_list(symm.pfmla_list_id, vbl->pfmla_idx);

  const PFmlaVbl& pf_vbl = this->pfmla_vbl(*vbl);
  this->identity_xn &= pf_vbl.img_eq(pf_vbl);
  this->xfmlae_ctx.identity_xn &= pf_vbl.img_eq(pf_vbl);

  if (symm.pure_shadow_ck()) {
    pure_shadow_vbl_exists = true;
    pfmla_ctx.add_to_vbl_list (pure_shadow_pfmla_list_id, vbl->pfmla_idx);
  }
  if (symm.pure_puppet_ck()) {
    pure_puppet_vbl_exists = true;
    pfmla_ctx.add_to_vbl_list (pure_puppet_pfmla_list_id, vbl->pfmla_idx);
  }
  if (symm.shadow_ck()) {
    pfmla_ctx.add_to_vbl_list (shadow_pfmla_list_id, vbl->pfmla_idx);
  }
  if (symm.puppet_ck()) {
    pfmla_ctx.add_to_vbl_list (puppet_pfmla_list_id, vbl->pfmla_idx);
  }
}

  void
Net::commit_variables()
{
  Table< Tuple<uint,2> > sizes(vbl_symms.sz());
  uint refsz = 1;
  uint maxsz = 0;
  for (uint i = 0; i < vbl_symms.sz(); ++i) {
    VblSymm& symm = vbl_symms[i];
    sizes[i][0] = symm.membs.sz();
    sizes[i][1] = i;
    if (refsz == 1 && symm.membs.sz() > refsz) {
      refsz = symm.membs.sz();
    }
    if (symm.membs.sz() > 1 && symm.membs.sz() < refsz) {
      refsz = symm.membs.sz();
    }
    if (symm.membs.sz() > maxsz) {
      maxsz = symm.membs.sz();
    }
  }
  std::sort (sizes.begin(), sizes.end());
  for (uint cut_i = 0; cut_i < refsz; ++cut_i) {
    for (uint i = 0; i < vbl_symms.sz(); ++i) {
      VblSymm& symm = vbl_symms[sizes[i][1]];
      uint stride = ceil_quot(symm.membs.sz(), refsz);
      for (uint j = cut_i * stride; j < symm.membs.sz() && j < (cut_i+1) * stride; ++j) {
        commit_variable(symm, j);
      }
    }
  }
}

  PcSymm*
Net::add_processes(const String& name, const String& idx_name, uint nmembs)
{
  if (vbls.sz() == 0) {
    commit_variables();
  }
  PcSymm& symm = pc_symms.grow1();
  symm.spec = &spec->pc_symms.grow1();
  symm.spec->name = name;
  symm.spec->nmembs_expression = nmembs;
  symm.spec->idx_name = idx_name;
  for (uint i = 0; i < nmembs; ++i) {
    xfmlae_ctx.wvbl_list_ids.push(pfmla_ctx.add_vbl_list());
    Pc& pc = pcs.push(Pc(&symm, i));
    symm.membs.push(&pc);
    symm.mapped_indices.membs.push(i);
    if (this->featherweight)  continue;
    pc.global_mask_xn = this->identity_xn;
    xfmlae_ctx.global_mask_xns.push(this->identity_xn);
  }
  return &symm;
}

  void
Net::add_access (PcSymm* pc_symm, const VblSymm* vbl_symm,
                 const NatMap& indices,
                 Xn::VariableAccessType access_type)
{
  Xn::PcSymmSpec* spec = +pc_symm->spec;
  pc_symm->rvbl_symms.push(vbl_symm);
  pc_symm->vbl_indices.push(indices);

  Xn::VblSymmAccessSpec& access = spec->access.grow1();
  access.vbl_symm = +vbl_symm->spec;
  access.type = access_type;
  access.index_expression = indices.expression;

  if (access.write_ck()) {
    spec->wmap.push(spec->access.sz()-1);
    pc_symm->wvbl_symms.push(vbl_symm);
  }

  for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
    Vbl& vbl = *vbl_symm->membs[indices.index(i, vbl_symm->membs.sz())];
    Pc& pc = *pc_symm->membs[i];
    pc.rvbls.push(&vbl);

    if (access.random_read_ck()) {
      vbl.random_flag = true;
    }

    if (!access.write_ck())  continue;

    pc.wvbls.push(&vbl);

    if (this->featherweight)  continue;

    pc.global_mask_xn =
      pc.global_mask_xn.smooth(pfmla_vbl(vbl));

    const uint pcidx = this->pcs.index_of(&pc);
    pfmla_ctx.add_to_vbl_list(xfmlae_ctx.wvbl_list_ids[pcidx],
                              vbl.pfmla_idx);
    xfmlae_ctx.global_mask_xns[pcidx] =
      xfmlae_ctx.global_mask_xns[pcidx].smooth(pfmla_vbl(vbl));
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

  uint
Net::representative_action_index(uint actidx) const
{
  Xn::ActSymm act;
  this->action(act, actidx);
  const Xn::PcSymm& pc_symm = *act.pc_symm;
  const Xn::PcSymmSpec& pc_symm_spec = *pc_symm.spec;

  bool changed = true;
  while (changed) {
    changed = false;
    for (uint linksymm_idx = 0; linksymm_idx < pc_symm_spec.link_symmetries.sz(); ++linksymm_idx) {
      const LinkSymmetry& ob = pc_symm_spec.link_symmetries[linksymm_idx];

      for (uint link_idx = 0; link_idx < ob.nlinks-1; ++link_idx) {
        Xn::ActSymm act_tmp( act );
        for (uint vbl_idx = 0; vbl_idx < ob.nvbls; ++vbl_idx) {
          act_tmp.swap_vals(ob(vbl_idx, link_idx), ob(vbl_idx, link_idx+1));
        }
        if (act_tmp.vals < act.vals) {
          act = act_tmp;
          changed = true;
        }
      }
    }
  }

  for (uint vbl_idx = 0; vbl_idx < pc_symm.rvbl_symms.sz(); ++vbl_idx) {
    const Xn::VblSymm& vbl_symm = *pc_symm.rvbl_symms[vbl_idx];
    if (vbl_symm.pure_shadow_ck()) {
      act.vals[vbl_idx] = 0;
    }
  }

  uint rep_actidx = this->action_index(act);
  Claim2( rep_actidx ,<=, actidx );
  return rep_actidx;
}

  const X::Fmla
Net::action_pfmla(uint actidx) const
{
  if (!this->lightweight) {
    return act_xfmlaes[actidx].xfmla();
  }
  X::Fmla xn(false);
  const Table<uint>& actions = represented_actions[actidx];
  for (uint i = 0; i < actions.sz(); ++i) {
    X::Fmla tmp_xn;
    this->make_action_pfmla(&tmp_xn, actions[i]);
    xn |= tmp_xn;
  }
  const Xn::PcSymm& pc_symm = pc_symms[this->action_pcsymm_index(actidx)];
  if (!pc_symm.spec->random_write_ck()) {
    xn -= xn.img();
  }
  return xn;
}

  const X::Fmlae
Net::action_xfmlae(uint actidx) const
{
  if (!this->lightweight) {
    return act_xfmlaes[actidx];
  }
  X::Fmlae xn(&this->xfmlae_ctx);
  const Table<uint>& actions = represented_actions[actidx];
  for (uint i = 0; i < actions.sz(); ++i) {
    X::Fmlae tmp_xn;
    this->make_action_xfmlae(&tmp_xn, actions[i]);
    xn |= tmp_xn;
  }
  const Xn::PcSymm& pc_symm = pc_symms[this->action_pcsymm_index(actidx)];
  if (!pc_symm.spec->random_write_ck()) {
    xn.self_disable();
  }
  return xn;
}

  bool
Net::safe_ck(const Xn::ActSymm& act) const
{
  const PcSymm& pc_symm = *act.pc_symm;
  if (pc_symm.membs.sz() == 0)  return true;
  uint pcidx = 0;
  pc_symm.representative(&pcidx);
  const Pc& pc = *pc_symm.membs[pcidx];
  const X::Fmla& xn = this->represented_xns_of_pc(act, pcidx);
  if (pc.permit_xn.sat_ck()) {
    if (!xn.subseteq_ck(pc.permit_xn))
      return false;
  }
  if (pc.forbid_xn.sat_ck()) {
    if (xn.subseteq_ck(pc.forbid_xn))
      return false;
  }
  return true;
}

  void
Net::unroll_action(Table<Xn::ActSymm>& dst, uint actid, bool include_shadow) const
{
  Xn::ActSymm act;
  this->action(act, actid);
  const Xn::PcSymm& pc_symm = *act.pc_symm;
  const Xn::PcSymmSpec& pc_spec = *pc_symm.spec;
  uint pcidx = 0;
  if (!pc_symm.representative(&pcidx)) {
    DBog0("Cannot find a process with unique variable accesses!");
    return;
  }
  const Xn::Pc& pc = *pc_symm.membs[pcidx];
  X::Fmla pc_xn = represented_xns_of_pc(act, pcidx);
  pc_xn &= pc.closed_assume;

  Table<uint> rvbl_idcs;
  Table<uint> pfmla_rvbl_idcs;
  for (uint ridx = 0; ridx < pc_spec.access.sz(); ++ridx) {
    const VblSymmAccessSpec& access = pc_spec.access[ridx];
    act.guard(ridx) = 0;
    if (!include_shadow && access.pure_shadow_ck())  continue;
    if (!access.synt_read_ck() && !access.synt_writeonly_ck())  continue;
    rvbl_idcs << ridx;
    pfmla_rvbl_idcs << pc.rvbls[ridx]->pfmla_idx;
  }

  Table<uint> wvbl_idcs;
  Table<uint> pfmla_wvbl_idcs;
  for (uint widx = 0; widx < pc_spec.wmap.sz(); ++widx) {
    const VblSymmAccessSpec& access = pc_spec.waccess(widx);
    act.assign(widx) = 0;
    if (access.random_ck())  continue;
    if (!access.write_ck())  continue;
    if (!include_shadow && access.pure_shadow_ck())  continue;
    wvbl_idcs << widx;
    pfmla_wvbl_idcs << pc.wvbls[widx]->pfmla_idx;
  }


  Table<uint> pre_state( rvbl_idcs.sz() );
  Table<uint> img_state( wvbl_idcs.sz() );

  while (pc_xn.sat_ck()) {
    pc_xn.state(&pre_state[0], pfmla_rvbl_idcs);
    P::Fmla pre_pf = pfmla_ctx.pfmla_of_state(&pre_state[0], pfmla_rvbl_idcs);
    P::Fmla img_pf = pc_xn.img(pre_pf);
    pc_xn -= pre_pf;

    for (uint i = 0; i < pre_state.sz(); ++i) {
      act.guard(rvbl_idcs[i]) = pre_state[i];
    }

    while (img_pf.sat_ck()) {
      img_pf.state(&img_state[0], pfmla_wvbl_idcs);
      img_pf -= pfmla_ctx.pfmla_of_state(&img_state[0], pfmla_wvbl_idcs);

      for (uint i = 0; i < img_state.sz(); ++i) {
        act.assign(wvbl_idcs[i]) = img_state[i];
      }
      dst << act;
    }
  }
}


  ostream&
Net::oput(ostream& of,
          const P::Fmla& pf,
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

  OFile&
Net::oput_vbl_names(OFile& of) const
{
  for (uint i = 0; i < this->vbls.sz(); ++i) {
    if (i > 0)
      of << ' ';
    of << name_of (this->vbls[i]);
  }
  of << '\n';
  return of;
}

  OFile&
Net::oput_pfmla(OFile& of, Cx::PFmla pf,
                Sign pre_or_img, bool just_one) const
{
  Table<uint> state_pre(this->vbls.sz(), 0);
  Table<uint> state_img(this->vbls.sz(), 0);
  while (pf.sat_ck())
  {
    P::Fmla pf_pre = pf.pick_pre();
    P::Fmla pf_img = pf.img(pf_pre).pick_pre();

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


  OFile&
Net::oput_one_xn(OFile& of, const X::Fmla& pf) const
{
  return this->oput_pfmla(of, pf, 0, true);
}

  OFile&
Net::oput_all_xn(OFile& of, const X::Fmla& pf) const
{
  return this->oput_pfmla(of, pf, 0, false);
}

  OFile&
Net::oput_one_pf(OFile& of, const P::Fmla& pf) const
{
  return this->oput_pfmla(of, pf, -1, true);
}

  OFile&
Net::oput_all_pf(OFile& of, const P::Fmla& pf) const
{
  return this->oput_pfmla(of, pf, -1, false);
}


  void
Sys::commit_initialization()
{
  Xn::Net& topo = this->topology;
  topo.commit_initialization();

  if (topo.featherweight)  return;

  this->shadow_self = true;

  for (uint i = 0; i < topo.vbls.sz(); ++i) {
    const Xn::Vbl& vbl = topo.vbls[i];
    if (vbl.symm->pure_shadow_ck()) {
      shadow_puppet_synthesis = true;
    }
    if (vbl.symm->pure_puppet_ck()) {
      shadow_puppet_synthesis = true;
    }
    if (vbl.symm->shadow_ck()) {
      const PFmlaVbl& x = topo.pfmla_ctx.vbl(vbl.pfmla_idx);
      shadow_self &= (x.img_eq(x));
    }
  }

  this->direct_pfmla = false;
  for (uint i = 0; i < topo.pc_symms.sz(); ++i) {
    PcSymm& pc_symm = topo.pc_symms[i];
    pc_symm.direct_pfmla = false;
    for (uint j = 0; j < pc_symm.membs.sz(); ++j) {
      const Pc& pc = *pc_symm.membs[j];
      pc_symm.direct_pfmla |=
        pc.puppet_xn
        & pc.closed_assume
        & pc.global_mask_xn;
    }
    this->direct_pfmla |= pc_symm.direct_pfmla;
  }

#if 1
  Set<uint> tmp_action_set;
  for (uint i = 0; i < topo.pc_symms.sz(); ++i) {
    const PcSymm& pc_symm = topo.pc_symms[i];
    Table<uint> tmp_actions;
    pc_symm.actions(tmp_actions, topo.pfmla_ctx);
    for (uint j = 0; j < tmp_actions.sz(); ++j) {
      tmp_action_set << topo.representative_action_index(tmp_actions[j]);
    }
  }
  this->actions.assign(tmp_action_set.begin(), tmp_action_set.end());
#else
  for (uint act_idx = 0; act_idx < topo.n_possible_acts; ++act_idx) {
    const X::Fmla& act_pfmla = topo.action_pfmla(act_idx);
    if (act_pfmla.subseteq_ck(this->direct_pfmla) && act_pfmla.sat_ck()) {
      this->actions.push_back(act_idx);
    }
    else {
      // This may not hold when multiple processes can write to the same variable.
      //Claim( !act_pfmla.overlap_ck(this->direct_pfmla) );
    }
  }
#endif
}

  bool
Sys::integrityCk() const
{
  DeclLegit( good );
  const Net& topo = this->topology;

  if (topo.featherweight)  return true;

  Claim(topo.identity_xn.sat_ck());
  Claim(topo.identity_xn.subseteq_ck(this->shadow_self));
  Claim(topo.proj_shadow(topo.identity_xn).equiv_ck(this->shadow_self));

  for (uint i = 0; i < topo.pc_symms.sz(); ++i) {
    const Xn::PcSymmSpec& pc_symm_spec = topo.spec->pc_symms[i];
    for (uint j = 0; j < pc_symm_spec.access.sz(); ++j) {
      if (pc_symm_spec.access[j].random_read_ck()) {
        DoLegitLine( "Can only 'random read' with puppet variables!" )
          pc_symm_spec.access[j].vbl_symm->pure_puppet_ck();
      }
    }
  }

  if (false)
  for (uint i = 0; i < topo.pcs.sz(); ++i) {
    const Xn::Pc& pc = topo.pcs[i];
    for (uint j = 0; j < pc.rvbls.sz(); ++j) {
      if (!pc.symm->write_ck(j)) {
        DBog2( "%u %u", pc.rvbls[j]->pfmla_idx, i );
      }
    }
  }

  if (false)
  if (this->shadow_pfmla.overlap_ck(this->shadow_self)) {
    DBog0( "Error: Shadow protocol contains self-loops!" );
    good = false;
  }

  DoLegitLine( "Error: Invariant is empty!" )
    this->invariant.sat_ck();

  DoLegitLine( "Error: Invariant includes non-shadow variables." )
    topo.smooth_shadow_vbls(invariant).tautology_ck();

  if (false)
  if (!(this->shadow_pfmla.img(this->invariant) <= this->invariant)) {
    DBog0( "Error: Protocol is not closed in the invariant!" );
    good = false;

    X::Fmla bad_xn = this->shadow_pfmla & this->invariant & (~this->invariant).as_img();
    OFile of( stderr_OFile () );
    topo.oput_one_xn(of, bad_xn);
  }

  return !!good;
}

}

  OFile&
OPut(OFile& of, const Xn::ActSymm& act)
{
  const Xn::PcSymm& pc = *act.pc_symm;
  of << "/*" << pc.spec->name << "[" << pc.spec->idx_name << "]" << "*/ ";
  const char* delim = "";
  for (uint i = 0; i < pc.rvbl_symms.sz(); ++i) {
    if (!pc.spec->access[i].synt_read_ck())
      continue;
    of << delim;
    delim = " && ";
    of << pc.rvbl_symms[i]->spec->name
      << "[" << pc.spec->access[i].index_expression << "]"
      << "==" << act.guard(i);
  }
  of << " -->";
  for (uint i = 0; i < pc.wvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc.wvbl_symms[i];
    if (pc.spec->waccess(i).synt_writeonly_ck() && act.assign(i)==vbl_symm.domsz)
      continue;
    of << ' ' << vbl_symm.spec->name
      << "[" << pc.spec->waccess(i).index_expression << "]"
      << ":=";
    if (pc.spec->waccess(i).random_write_ck())
      of << '_';
    else
      of << act.assign(i);
    of << ';';
  }
  return of;
}

  void
find_one_cycle(Table<P::Fmla>& states, const X::Fmla& xn, const P::Fmla& scc, const P::Fmla& initial)
{
  states.clear();
  states.push( initial.pick_pre() );
  P::Fmla visit( false );

  while (true) {
    visit |= states.top();
    const P::Fmla& next = scc & xn.img(states.top());
    Claim( next.sat_ck() );
    if (next.overlap_ck(visit)) {
      states.push( (next & visit).pick_pre() );
      break;
    }
    states.push(next.pick_pre());
  }

  uint start_idx = 0;
  for (uint i = 0; i < states.sz(); ++i) {
    if (states[i].equiv_ck(states.top())) {
      start_idx = i;
      break;
    }
  }

  for (uint i = 0; i + start_idx < states.sz(); ++i) {
    states[i] = states[i+start_idx];
  }
  states.mpop(start_idx);
}

  void
find_one_cycle(Table<P::Fmla>& states, const X::Fmla& xn, const P::Fmla& scc)
{
  find_one_cycle(states, xn, scc, scc);
}

  void
find_livelock_actions(Table<uint>& ret_actions, const X::Fmla& xn,
                      const P::Fmla& scc, const P::Fmla& invariant,
                      const Xn::Net& topo)
{
  Table<uint> actions(ret_actions);
  ret_actions.clear();
  Table<P::Fmla> states;
  find_one_cycle(states, xn, scc, scc - invariant);
  bool livelock_found = false;
  for (uint i = 0; i < states.sz()-1 && !livelock_found; ++i) {
    if (!states[i].overlap_ck(invariant)) {
      livelock_found = true;
    }
  }

  if (!livelock_found) {
    for (uint j = 0; j < actions.size(); ++j) {
      uint actidx = actions[j];
      const X::Fmla& act_xn = topo.action_pfmla(actidx);
      if (act_xn.img(scc).overlap_ck(scc)) {
        ret_actions.push(actidx);
      }
    }
    return;
  }

  Set<uint> livelock_set;
  for (uint i = 0; i < states.sz()-1; ++i) {
    for (uint j = 0; j < actions.size(); ++j) {
      uint actidx = actions[j];
      const X::Fmla& act_xn = topo.action_pfmla(actidx);
      if (act_xn.img(states[i]).overlap_ck(states[i+1])) {
        livelock_set << actidx;
        continue;
      }
    }
  }
  livelock_set.fill(ret_actions);
}

  void
oput_one_cycle(OFile& of, const X::Fmla& xn,
               const P::Fmla& scc, const P::Fmla& initial,
               const Xn::Net& topo)
{
  Table<P::Fmla> states;
  find_one_cycle(states, xn, scc, initial);
  of << "Cycle is:\n";
  for (uint i = 0; i < states.sz(); ++i) {
    topo.oput_pfmla(of, states[i], -1, true);
  }
  of.flush();
}

  X::Fmla
Xn::Net::sync_xn(const Table<uint>& actidcs, const bool fully_synchronous) const
{
  X::Fmlae xfmlae(&this->xfmlae_ctx);
  Set<uint> all_actidcs_set;
  for (uint i = 0; i < actidcs.sz(); ++i) {
    const Table<uint>& all_acts =
      represented_actions[actidcs[i]];
    for (uint j = 0; j < all_acts.sz(); ++j) {
      all_actidcs_set << all_acts[j];
    }
  }

  FlatSet<uint> all_actidcs( all_actidcs_set );

  for (uint i = 0; i < all_actidcs.sz(); ++i) {
    ActSymm act;
    this->action(act, all_actidcs[i]);
    const Xn::PcSymm& pc_symm = *act.pc_symm;
    for (uint symmidx = 0; symmidx < pc_symm.membs.sz(); ++symmidx) {
      const uint pcidx = this->pcs.index_of(pc_symm.membs[symmidx]);
      xfmlae[pcidx] |= xn_of_pc(act, symmidx);
    }
  }

  BitTable written_vbls( vbls.sz(), 0 );

  X::Fmla xn(true);
  for (uint pcidx = 0; pcidx < this->pcs.sz(); ++pcidx) {
    const Xn::Pc& pc = this->pcs[pcidx];
    P::Fmla self_loop( true );
    for (uint i = 0; i < pc.wvbls.sz(); ++i) {
      const PFmlaVbl& vbl = this->pfmla_vbl(*pc.wvbls[i]);
      self_loop &= vbl.img_eq(vbl);

      const uint xnvbl_idx = vbls.index_of(pc.wvbls[i]);
      if (1 == written_vbls[xnvbl_idx]) {
        const char msg[] = "Two processes cannot write to the same variable in a synchronous system!";
        DBog0( msg );
        failout_sysCx (msg);
      }
      written_vbls[xnvbl_idx] = 1;
    }
    if (fully_synchronous) {
      self_loop -= xfmlae[pcidx].pre();
    }
    xn &= (self_loop | xfmlae[pcidx]);
  }

  X::Fmla read_only_identity_xn( true );
  for (uint i = 0; i < written_vbls.sz(); ++i) {
    if (1 == written_vbls[i])
      continue;
    const PFmlaVbl& vbl = pfmla_vbl(vbls[i]);
    read_only_identity_xn &= vbl.img_eq(vbl);
  }
  xn &= read_only_identity_xn;
  xn -= this->identity_xn;
  return xn;
}

  X::Fmla
Xn::Net::semisync_xn(const Table<uint>& actidcs) const
{
  return this->sync_xn(actidcs, false);
}

/**
 * Ensure {pcidx} is relative to {act.pc_symm}.
 **/
  X::Fmla
Xn::Net::xn_of_pc(const Xn::ActSymm& act, uint pcidx) const
{
  const Xn::PcSymm& pc_symm = *act.pc_symm;
  const Xn::Pc& pc = *pc_symm.membs[pcidx];
  // Local transition whose guard is over puppet variables
  // but does make an assignment to the writeable pure shadow variables.
  X::Fmla xn(true);

  bool readable_self_loop = true;
  bool probabilistic = false;
  for (uint i = 0; i < pc.wvbls.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.wvbl_symms[i];
    const PFmlaVbl& vbl = pfmla_vbl(*pc.wvbls[i]);
    bool random_write =
      pc_symm.spec->waccess(i).random_write_ck();

    if (pc_symm.spec->waccess(i).synt_read_ck()) {
      if (random_write) {
        probabilistic = true;
      }
      else if (act.aguard(i) != act.assign(i)) {
        readable_self_loop = false;
      }
      xn &= (vbl == act.aguard(i));
    }

    if (random_write) {
    }
    else if (act.assign(i)==vbl_symm.domsz) {
      Claim( pc_symm.spec->waccess(i).synt_writeonly_ck() );
      xn &= vbl.identity();
    }
    else {
      xn &= vbl.img_eq(act.assign(i));
    }
  }
  if (probabilistic) {
    readable_self_loop = false;
    const uint global_pcidx = pcs.index_of(&pc);
    const uint wvbl_list_id = xfmlae_ctx.wvbl_list_ids[global_pcidx];

    P::Fmla okay_xn( pc.closed_assume );
    okay_xn &= pc.closed_assume.subst_to_img(wvbl_list_id);
    // TODO: Next line is bad.
    okay_xn &= ~pc.forbid_xn;
    if (pc.permit_xn.sat_ck()) {
      okay_xn &= pc.permit_xn;
    }
    xn &= okay_xn;
  }

  // When there is a self-loop on puppet variables,
  // ensure that some write-only variable changes in the X::Fmla.
  if (readable_self_loop) {
    P::Fmla writeonly_guard( false );
    for (uint i = 0; i < pc.wvbls.sz(); ++i) {
      const PFmlaVbl& vbl = pfmla_vbl(*pc.wvbls[i]);
      if (pc_symm.spec->waccess(i).synt_writeonly_ck()
          && act.assign(i) < pc_symm.wvbl_symms[i]->domsz)
      {
        writeonly_guard |= (vbl != act.assign(i));
      }
    }
    xn &= writeonly_guard;
  }

  for (uint i = 0; i < pc.rvbls.sz(); ++i) {
    const PFmlaVbl& vbl = pfmla_vbl(*pc.rvbls[i]);
    if (pc_symm.spec->access[i].synt_readonly_ck()) {
      xn &= (vbl == act.guard(i));
    }
  }

  return xn;
}

/**
 * Ensure {pcidx} is relative to {act.pc_symm}.
 **/
  X::Fmla
Xn::Net::represented_xns_of_pc(const Xn::ActSymm& act, uint relative_pcidx) const
{
  uint actidx = this->action_index(act);
  const Xn::Pc* pc = act.pc_symm->membs[relative_pcidx];
  if (!this->lightweight) {
    uint real_pcidx = this->pcs.index_of(pc);
    return act_xfmlaes[actidx][real_pcidx];
  }
  const Table<uint>& reps =
    this->represented_actions[actidx];
  X::Fmla xn( false );
  for (uint i = 0; i < reps.sz(); ++i) {
    ActSymm tmp_act;
    this->action(tmp_act, reps[i]);
    xn |= this->xn_of_pc(tmp_act, relative_pcidx);
  }
  if (!act.pc_symm->spec->random_write_ck()) {
    xn -= (xn & pc->global_mask_xn).img();
  }
  return xn;
}

  void
Xn::Net::make_action_pfmla(X::Fmla* ret_xn, uint actidx) const
{
  X::Fmlae xn(&this->xfmlae_ctx);
  this->make_action_xfmlae(&xn, actidx);
  if (ret_xn) {
    *ret_xn = xn.xfmla();
  }
}

  void
Xn::Net::make_action_xfmlae(X::Fmlae* ret_xn, uint actidx) const
{
  Xn::ActSymm act;
  this->action(act, actidx);
  const Xn::PcSymm& pc_symm = *act.pc_symm;

  uint offset = 0;
  if (pc_symm.membs.sz() > 0) {
    offset = this->pcs.index_of(pc_symm.membs[0]);
  }

  X::Fmlae xn(&this->xfmlae_ctx);
  for (uint pc_memb_idx = 0; pc_memb_idx < pc_symm.membs.sz(); ++pc_memb_idx) {
    xn[offset+pc_memb_idx] |= this->xn_of_pc(act, pc_memb_idx);
  }

  if (ret_xn) {
    *ret_xn = xn;
  }
}

/**
 * Create a persistent PF for this action.
 * \sa commit_initialization()
 **/
  void
Xn::Net::cache_action_xfmla(uint actidx)
{
  X::Fmlae xn(&this->xfmlae_ctx);
  make_action_xfmlae(&xn, actidx);

  uint rep_actidx = representative_action_index(actidx);

  if (rep_actidx == actidx) {
    act_xfmlaes[actidx] = xn;
  }
  else {
    act_xfmlaes[actidx] = false;
    act_xfmlaes[rep_actidx] |= xn;
  }
  const Xn::PcSymm& pc_symm = pc_symms[this->action_pcsymm_index(actidx)];
  if (!pc_symm.spec->random_write_ck()) {
    act_xfmlaes[rep_actidx].self_disable();
  }
}

  bool
candidate_actions(std::vector<uint>& candidates,
                  Table<uint>& dels,
                  Table<uint>& rejs,
                  const Xn::Sys& sys)
{
  const Xn::Net& topo = sys.topology;

  if (!sys.invariant.sat_ck()) {
    DBog0( "Invariant is empty!" );
    return false;
  }

  const P::Fmla& hi_invariant = (sys.invariant & sys.closed_assume);

  if (!hi_invariant.sat_ck()) {
    DBog0( "Invariant is empty with (assume & closed) predicate!" );
    return false;
  }

  if (sys.invariant.tautology_ck()) {
    DBog0( "All states are invariant!" );
    if (!sys.shadow_puppet_synthesis_ck()) {
      return true;
    }
  }

  for (uint actidx = 0; actidx < topo.n_possible_acts; ++actidx) {
    const bool explain_rej = false;

    if (actidx != topo.representative_action_index(actidx)) {
      continue;
    }

    bool add = true;

    Xn::ActSymm act;
    topo.action(act, actidx);
    const Xn::PcSymm& pc_symm = *act.pc_symm;
    if (pc_symm.membs.sz() == 0)
      continue;

    uint rep_pcidx = 0;
    pc_symm.representative(&rep_pcidx);
    const Xn::Pc& pc = *pc_symm.membs[rep_pcidx];
    const X::Fmla& pc_xn = topo.represented_xns_of_pc(act, rep_pcidx);

    const X::Fmla& act_xn = topo.action_pfmla(actidx);
    if (!act_xn.sat_ck()) {
      add = false;
    }
    if (add) {
      add = !pc_xn.subseteq_ck(pc.forbid_xn);
      if (!add) {
        rejs << actidx;
      }
    }
    if (add) {
      if (pc.permit_xn.sat_ck()) {
        if (!pc_xn.subseteq_ck(pc.permit_xn)) {
          add = false;
          rejs << actidx;
        }
      }
    }

    // Check for self-loops.
    bool puppet_selfloop = true;
    bool shadow_selfloop = true;
    bool shadow_full_img = true;
    bool shadow_exists = false;
    //X::Fmla shadow_xn = topo.smooth_puppet_vbls(pc.shadow_xn.img());
    X::Fmla shadow_xn = topo.smooth_puppet_vbls(pc.shadow_xn);
    if (add) {
      for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
        const Xn::VblSymmAccessSpec& access = pc_symm.spec->waccess(i);

        const Xn::VblSymm& vbl_symm = *pc_symm.wvbl_symms[i];
        const Xn::Vbl& vbl = *pc.wvbls[i];
        const PFmlaVbl& pf_vbl = topo.pfmla_vbl(vbl);
        if (vbl_symm.pure_shadow_ck()) {
          shadow_exists = true;
          if (act.assign(i) == vbl_symm.domsz) {
            shadow_xn &= pf_vbl.img_eq(pf_vbl);
            shadow_full_img = false;
          }
          else {
            shadow_selfloop = false;
            shadow_xn &= pf_vbl.img_eq(act.assign(i));
            shadow_xn = shadow_xn.smooth_pre(pf_vbl);
          }
        }
        else if (access.random_write_ck()) {
          puppet_selfloop = false;
        }
        else if (access.synt_writeonly_ck()) {
          if (act.assign(i) != vbl_symm.domsz) {
            puppet_selfloop = false;
          }
        }
        else if (act.assign(i) != act.aguard(i)) {
          puppet_selfloop = false;
        }
      }
      for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
        if (pc_symm.write_ck(i))  continue;
        const Xn::VblSymm& vbl_symm = *pc_symm.rvbl_symms[i];
        if (vbl_symm.puppet_ck())  continue;
        const PFmlaVbl& pf_vbl = topo.pfmla_vbl(*pc.rvbls[i]);
        shadow_xn = shadow_xn.smooth(pf_vbl);
      }

      if (puppet_selfloop && shadow_selfloop) {
        add = false;
        rejs << actidx;
        if (explain_rej) {
          OPut((DBogOF << "Action " << actidx << " is a self-loop: "), act) << '\n';
        }
      }
      if (!shadow_exists)
        shadow_selfloop = false;
    }

    if (add && !act_xn.img(sys.closed_assume).subseteq_ck(sys.closed_assume)) {
      add = false;
      rejs << actidx;
      if (explain_rej) {
        OPut((DBogOF << "Action " << actidx << " leaves assumed states: "), act) << '\n';
      }
    }
    if (add && !sys.closed_assume.overlap_ck(act_xn.pre())) {
      add = false;
      dels << actidx;
    }
    // Optimization. Shadow variables can just be changed as if the invariant
    // is reached or will be reached by this action.
    if (add && !topo.smooth_puppet_vbls(act_xn.img()).overlap_ck(hi_invariant)) {
      add = false;
      dels << actidx;
    }

    if (!add) {
    }
    else if (!pc.shadow_xn.sat_ck()) {
      // When the shadow protocol is silent, at least for this process,
      // then we enforce every action to assign the pure shadow variables.
      if (!shadow_full_img) {
        add = false;
        rejs << actidx;
      }
    }
    else if (hi_invariant.subseteq_ck(sys.shadow_pfmla.pre()) && puppet_selfloop) {
      add = false;
      rejs << actidx;
    }
    else if (shadow_selfloop || puppet_selfloop) {
      if (sys.spec->active_shadow_ck()) {
        add = false;
        rejs << actidx;
      }
    }
    else if (hi_invariant.subseteq_ck(sys.shadow_pfmla.pre())
             || sys.spec->active_shadow_ck())
    {
      // Optimization. When the shadow protocol is never silent in the invariant,
      // pure shadow variables should only change as they do in the shadow protocol.
      if (!topo.smooth_puppet_vbls(pc_xn).equiv_ck(shadow_xn)) {
        add = false;
        dels << actidx;
      }
    }

    if (add && sys.spec->invariant_scope == Xn::DirectInvariant) {
      if (!act_xn.img(hi_invariant).subseteq_ck(sys.invariant)) {
        add = false;
        rejs << actidx;
        if (explain_rej) {
          OPut((DBogOF << "Action " << actidx << " breaks closure: "), act) << '\n';
        }
      }
      else if (sys.spec->invariant_style != Xn::FutureAndClosed &&
               !(act_xn & hi_invariant)
               .subseteq_ck(sys.shadow_pfmla | sys.shadow_self))
      {
        add = false;
        rejs << actidx;
        if (explain_rej) {
          OPut((DBogOF << "Action " << actidx << " breaks shadow protocol: "), act) << '\n';
        }
      }
    }
    if (add && !act_xn.pre().overlap_ck(sys.closed_assume)) {
      add = false;
    }

    if (add) {
      candidates.push_back(actidx);
    }
  }
  if (candidates.size() == 0) {
    DBog0( "No candidates actions!" );
    return false;
  }

  return true;
}
END_NAMESPACE

