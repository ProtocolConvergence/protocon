
#include "xnsys.hh"
#include <cx/bittable.hh>

Cx::OFile DBogOF( stderr_OFile () );


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
      if (pc.rvbl_symms[j]->pure_shadow_ck()) {
        domsz = 1;
      }
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

  this->n_possible_acts = ntotal;
  represented_actions.resize(ntotal);
  for (uint actidx = 0; actidx < ntotal; ++actidx) {
    uint rep_actidx = representative_action_index(actidx);
    represented_actions[rep_actidx].push(actidx);
  }
  if (this->lightweight)
    return;
  act_pfmlas.resize(ntotal);
  for (uint i = 0; i < ntotal; ++i) {
    this->cache_action_pfmla(i);
  }
}

  VblSymm*
Net::add_variables(const String& name, uint nmembs, uint domsz,
                   Vbl::ShadowPuppetRole role)
{
  // Cannot add variables after committing them.
  Claim2( vbls.sz() ,==, 0 );

  VblSymm& symm = vbl_symms.grow1();
  symm.spec = &spec->vbl_symms.grow1();
  symm.domsz = domsz;
  symm.spec->name = name;
  symm.spec->domsz_expression = domsz;
  symm.spec->nmembs_expression = nmembs;
  symm.pfmla_list_id = pfmla_ctx.add_vbl_list();
  symm.shadow_puppet_role = role;
  symm.membs.grow(nmembs, 0);

  return &symm;
}

  void
Net::commit_variable(VblSymm& symm, uint i)
{
  Vbl* vbl = &vbls.push(Vbl(&symm, i));
  symm.membs[i] = vbl;
  vbl->pfmla_idx = pfmla_ctx.add_vbl(name_of (*vbl), symm.domsz);
  pfmla_ctx.add_to_vbl_list(symm.pfmla_list_id, vbl->pfmla_idx);

  const Cx::PFmlaVbl& pf_vbl = this->pfmla_vbl(*vbl);
  this->identity_xn &= pf_vbl.img_eq(pf_vbl);

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
  Cx::Table< Cx::Tuple<uint,2> > sizes(vbl_symms.sz());
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
    Pc& pc = pcs.push(Pc(&symm, i));
    symm.membs.push(&pc);
    pc.act_unchanged_pfmla = this->identity_xn;
  }
  return &symm;
}

  void
Net::add_read_access (PcSymm* pc_symm, const VblSymm* vbl_symm,
                      const NatMap& indices)
{
  pc_symm->rvbl_symms.push(vbl_symm);
  pc_symm->spec->rvbl_symms.push(+vbl_symm->spec);
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
  pc_symm->spec->wvbl_symms.push(+vbl_symm->spec);
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

  bool
PcSymm::dom_equiv_ck(const PcSymm& b) const
{
  const PcSymm& a = *this;
  if (a.n_possible_acts != b.n_possible_acts)
    return false;
  if (a.rvbl_symms.sz() != b.rvbl_symms.sz())
    return false;
  for (uint i = 0; i < a.rvbl_symms.sz(); ++i) {
    if (a.rvbl_symms[i]->domsz != b.rvbl_symms[i]->domsz)
      return false;
  }
  if (a.wvbl_symms.sz() != b.wvbl_symms.sz())
    return false;
  for (uint i = 0; i < a.wvbl_symms.sz(); ++i) {
    if (a.wvbl_symms[i]->domsz != b.wvbl_symms[i]->domsz)
      return false;
  }
  return true;
}

  bool
PcSymm::representative(uint* ret_pcidx) const
{
  for (uint i = 0; i < membs.sz(); ++i) {
    const Pc& pc = *membs[i];
    bool use = true;
    for (uint j = 0; j < pc.rvbls.sz(); ++j) {
      for (uint k = j+1; k < pc.rvbls.sz(); ++k) {
        if (pc.rvbls[j] == pc.rvbls[k]) {
          use = false;
        }
      }
    }
    for (uint j = 0; j < pc.wvbls.sz(); ++j) {
      for (uint k = j+1; k < pc.wvbls.sz(); ++k) {
        if (pc.wvbls[j] == pc.wvbls[k]) {
          use = false;
        }
      }
    }
    if (use) {
      if (ret_pcidx) {
        *ret_pcidx = i;
      }
      return true;
    }
  }
  return false;
}

static
  void
swap_pre_img (uint* vals, const Xn::PcSymm& pc_symm)
{
  uint off = pc_symm.rvbl_symms.sz();
  for (uint i = 0; i < pc_symm.wmap.sz(); ++i) {
    uint* pre_x = &vals[pc_symm.wmap[i]];
    uint* img_x = &vals[off + i];
    SwapT( uint, *pre_x, *img_x );
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
Pc::actions(Cx::Table<uint>& ret_actions, Cx::PFmlaCtx& ctx) const
{
  const Pc& pc = *this;
  const PcSymm& pc_symm = *pc.symm;

  Cx::Table<uint> pfmla_rvbl_idcs;
  for (uint i = 0; i < pc.rvbls.sz(); ++i) {
    pfmla_rvbl_idcs.push(pc.rvbls[i]->pfmla_idx);
  }
  Cx::Table<uint> pfmla_wvbl_idcs;
  for (uint i = 0; i < pc.wvbls.sz(); ++i) {
    pfmla_wvbl_idcs.push(pc.wvbls[i]->pfmla_idx);
  }

  Cx::PFmla pfmla( pc.puppet_xn );

  ActSymm act;
  act.vals.grow(pc.rvbls.sz() + pc.wvbls.sz());

  while (pfmla.sat_ck()) {
    uint* pre_state = &act.vals[0];
    pfmla.state(pre_state, pfmla_rvbl_idcs);
    Cx::PFmla pre_pf = ctx.pfmla_of_state(pre_state, pfmla_rvbl_idcs);
    Cx::PFmla img_pf = pfmla.img(pre_pf);

    for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
      if (pc_symm.rvbl_symms[i]->pure_shadow_ck()) {
        pre_state[i] = 0;
      }
    }
    while (img_pf.sat_ck()) {
      uint* img_state = &act.vals[pc.rvbls.sz()];
      img_pf.state(img_state, pfmla_wvbl_idcs);
      uint actidx = pc_symm.act_idx_offset +
        Cx::index_of_state (&act.vals[0], pc_symm.doms);
      ret_actions.push(actidx);
      img_pf -= ctx.pfmla_of_state(img_state, pfmla_wvbl_idcs);
    }
    pfmla -= pre_pf;
  }
}

  void
PcSymm::actions(Cx::Table<uint>& ret_actions, Cx::PFmlaCtx& ctx) const
{
  uint pcidx = 0;

#if 1
  Cx::Table<uint> pcidcs;
  if (this->representative(&pcidx)) {
    pcidcs.push(pcidx);
  }
  else {
    for (uint i = 0; i < membs.sz(); ++i) {
      pcidcs.push(i);
    }
    DBog0("System may not represent all actions!");
  }

  Set<uint> action_set;
  for (uint i = 0; i < pcidcs.sz(); ++i) {
    Cx::Table<uint> actions;
    membs[pcidcs[i]]->actions(actions, ctx);
    for (uint j = 0; j < actions.sz(); ++j) {
      action_set << actions[j];
    }
  }

  action_set.fill(ret_actions);
#else
  if (!this->representative(&pcidx)) {
    DBog0("System may not represent all actions!");
  }
  const Xn::Pc& pc = *this->membs[pcidx];
  Cx::PFmla xn = pc.direct_pfmla;
  while (xn.sat_ck()) {
    uint* pre_state = &act.vals[0];
    xn.state(pre_state, pfmla_rvbl_idcs);
    Cx::PFmla pre_pf = ctx.pfmla_of_state(pre_state, pfmla_rvbl_idcs);
    Cx::PFmla img_pf = pfmla.img(pre_pf);

    while (img_pf.sat_ck()) {
      uint* img_state = &act.vals[pc.rvbls.sz()];
      img_pf.state(img_state, pfmla_wvbl_idcs);
      uint actidx = pc_symm.act_idx_offset +
        Cx::index_of_state (&act.vals[0], pc_symm.doms);
      ret_actions.push(actidx);
      img_pf -= ctx.pfmla_of_state(img_state, pfmla_wvbl_idcs);
    }
    pfmla -= pre_pf;
  }
#endif

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
Net::oput_vbl_names(Cx::OFile& of) const
{
  for (uint i = 0; i < this->vbls.sz(); ++i) {
    if (i > 0)
      of << ' ';
    of << name_of (this->vbls[i]);
  }
  of << '\n';
  return of;
}

  Cx::OFile&
Net::oput_pfmla(Cx::OFile& of, Cx::PFmla pf,
                Sign pre_or_img, bool just_one) const
{
  Cx::Table<uint> state_pre(this->vbls.sz(), 0);
  Cx::Table<uint> state_img(this->vbls.sz(), 0);
  while (pf.sat_ck())
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
Net::oput_one_pf(Cx::OFile& of, const Cx::PFmla& pf) const
{
  return this->oput_pfmla(of, pf, -1, true);
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
    }
    if (vbl.symm->shadow_ck()) {
      const Cx::PFmlaVbl& x = topo.pfmla_ctx.vbl(vbl.pfmla_idx);
      shadow_self &= (x.img_eq(x));
    }
  }

#if 1
  Cx::Set<uint> tmp_action_set;
  for (uint i = 0; i < topo.pc_symms.sz(); ++i) {
    const PcSymm& pc_symm = topo.pc_symms[i];
    Cx::Table<uint> tmp_actions;
    pc_symm.actions(tmp_actions, topo.pfmla_ctx);
    for (uint j = 0; j < tmp_actions.sz(); ++j) {
      tmp_action_set << topo.representative_action_index(tmp_actions[j]);
    }
  }
  this->actions.assign(tmp_action_set.begin(), tmp_action_set.end());
#else
  for (uint act_idx = 0; act_idx < topo.n_possible_acts; ++act_idx) {
    const Cx::PFmla& act_pfmla = topo.action_pfmla(act_idx);
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
  bool good = true;
  const Net& topo = this->topology;

  Claim(topo.identity_xn.sat_ck());
  Claim(topo.identity_xn.subseteq_ck(this->shadow_self));
  Claim(topo.proj_shadow(topo.identity_xn).equiv_ck(this->shadow_self));

  if (false)
  for (uint i = 0; i < topo.pcs.sz(); ++i) {
    const Xn::Pc& pc = topo.pcs[i];
    for (uint j = 0; j < pc.rvbls.sz(); ++j) {
      if (!pc.symm->write_flags[j]) {
        DBog2( "%u %u", pc.rvbls[j]->pfmla_idx, i );
      }
    }
  }

  if (false)
  if (this->shadow_pfmla.overlap_ck(this->shadow_self)) {
    DBog0( "Error: Shadow protocol contains self-loops!" );
    good = false;
  }
  if (!this->invariant.sat_ck()) {
    DBog0( "Error: Invariant is empty!" );
    good = false;
  }
  else if (!topo.smooth_shadow_vbls(invariant).tautology_ck()) {
    DBog0( "Error: Invariant includes non-shadow variables." );
    good = false;
  }

  if (false)
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
  of << "/*" << pc.spec->name << "[" << pc.spec->idx_name << "]" << "*/ ";
  const char* delim = "";
  for (uint i = 0; i < pc.rvbl_symms.sz(); ++i) {
    if (pc.rvbl_symms[i]->pure_shadow_ck()) {
      continue;
    }
    of << delim;
    delim = " && ";
    of << pc.rvbl_symms[i]->spec->name
      << "[" << pc.rindices[i].expression << "]"
      << "==" << act.guard(i);
  }
  of << " -->";
  for (uint i = 0; i < pc.wvbl_symms.sz(); ++i) {
    of << ' ' << pc.wvbl_symms[i]->spec->name
      << "[" << pc.windices[i].expression << "]"
      << ":=" << act.assign(i) << ';';
  }
  return of;
}

  void
find_one_cycle(Cx::Table<Cx::PFmla>& states, const Cx::PFmla& xn, const Cx::PFmla& scc, const Cx::PFmla& initial)
{
  states.clear();
  states.push( initial.pick_pre() );
  Cx::PFmla visit( false );

  while (true) {
    visit |= states.top();
    const Cx::PFmla& next = scc & xn.img(states.top());
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
find_one_cycle(Cx::Table<Cx::PFmla>& states, const Cx::PFmla& xn, const Cx::PFmla& scc)
{
  find_one_cycle(states, xn, scc, scc);
}

  void
find_livelock_actions(Cx::Table<uint>& ret_actions, const Cx::PFmla& xn,
                      const Cx::PFmla& scc, const Cx::PFmla& invariant,
                      const Xn::Net& topo)
{
  Cx::Table<uint> actions(ret_actions);
  ret_actions.clear();
  Cx::Table<Cx::PFmla> states;
  find_one_cycle(states, xn, scc, scc - invariant);
  bool livelock_found = false;
  for (uint i = 0; i < states.sz()-1 && !livelock_found; ++i) {
    if (!states[i].overlap_ck(invariant)) {
      livelock_found = true;;
    }
  }

  if (!livelock_found) {
    states.resize(2);
    states[0] = scc;
    states[1] = scc;
  }

  for (uint i = 0; i < states.sz()-1; ++i) {
    for (uint j = 0; j < actions.size(); ++j) {
      uint actidx = actions[j];
      const Cx::PFmla& act_pfmla = topo.action_pfmla(actidx);
      if (states[i].overlap_ck(act_pfmla) &&
          states[i+1].as_img().overlap_ck(act_pfmla))
      {
        ret_actions.remove(actidx);
        ret_actions.push(actidx);
      }
    }
  }
}

  void
oput_one_cycle(Cx::OFile& of, const X::Fmla& xn,
               const P::Fmla& scc, const P::Fmla& initial,
               const Xn::Net& topo)
{
  Cx::Table<Cx::PFmla> states;
  find_one_cycle(states, xn, scc, initial);
  of << "Cycle is:\n";
  for (uint i = 0; i < states.sz(); ++i) {
    topo.oput_pfmla(of, states[i], -1, true);
  }
  of.flush();
}

  X::Fmla
Xn::Net::sync_xn(const Cx::Table<uint>& actidcs) const
{
  Cx::Table<P::Fmla> pc_xns(this->pcs.sz(), P::Fmla(false));
  Cx::Set<uint> all_actidcs_set;
  for (uint i = 0; i < actidcs.sz(); ++i) {
    const Cx::Table<uint>& all_acts =
      represented_actions[actidcs[i]];
    for (uint j = 0; j < all_acts.sz(); ++j) {
      all_actidcs_set << all_acts[j];
    }
  }

  Cx::FlatSet<uint> all_actidcs( all_actidcs_set );

  for (uint i = 0; i < all_actidcs.sz(); ++i) {
    ActSymm act;
    this->action(act, all_actidcs[i]);
    const Xn::PcSymm& pc_symm = *act.pc_symm;
    for (uint symmidx = 0; symmidx < pc_symm.membs.sz(); ++symmidx) {
      const uint pcidx = this->pcs.index_of(pc_symm.membs[symmidx]);
      pc_xns[pcidx] |= xn_of_pc(act, symmidx);
    }
  }

  Cx::BitTable written_vbls( vbls.sz(), 0 );

  X::Fmla xn(true);
  for (uint pcidx = 0; pcidx < this->pcs.sz(); ++pcidx) {
    const Xn::Pc& pc = this->pcs[pcidx];
    P::Fmla self_loop( true );
    for (uint i = 0; i < pc.wvbls.sz(); ++i) {
      const Cx::PFmlaVbl& vbl = this->pfmla_vbl(*pc.wvbls[i]);
      self_loop &= vbl.img_eq(vbl);

      const uint xnvbl_idx = vbls.index_of(pc.wvbls[i]);
      if (1 == written_vbls[xnvbl_idx]) {
        const char msg[] = "Two processes cannot write to the same variable in a synchronous system!";
        DBog0( msg );
        failout_sysCx (msg);
      }
      written_vbls[xnvbl_idx] = 1;
    }
    self_loop -= pc_xns[pcidx].pre();
    xn &= (self_loop | pc_xns[pcidx]);
  }

  X::Fmla read_only_identity_xn( true );
  for (uint i = 0; i < written_vbls.sz(); ++i) {
    if (1 == written_vbls[i])
      continue;
    const Cx::PFmlaVbl& vbl = pfmla_vbl(vbls[i]);
    read_only_identity_xn &= vbl.img_eq(vbl);
  }
  xn &= read_only_identity_xn;
  xn -= this->identity_xn;
  return xn;
}

  X::Fmla
Xn::Net::xn_of_pc(const Xn::ActSymm& act, uint pcidx) const
{
  const Xn::PcSymm& pc_symm = *act.pc_symm;
  const Xn::Pc& pc = *pc_symm.membs[pcidx];
  // Local transition whose guard is over puppet variables
  // but does make an assignment to the writeable pure shadow variables.
  X::Fmla xn(true);

  bool puppet_self_loop = true;
  for (uint i = 0; i < pc.wvbls.sz(); ++i) {
    const Cx::PFmlaVbl& vbl = pfmla_vbl(*pc.wvbls[i]);
    if (pc_symm.wvbl_symms[i]->puppet_ck()) {
      if (act.aguard(i) != act.assign(i)) {
        puppet_self_loop = false;
      }
      xn &= (vbl == act.aguard(i));
    }
    xn &= (vbl.img_eq(act.assign(i)));
  }

  // When there is a self-loop on puppet variables,
  // ensure that some shadow variable changes in the X::Fmla.
  if (puppet_self_loop) {
    P::Fmla shadow_guard( false );
    for (uint i = 0; i < pc.wvbls.sz(); ++i) {
      const Cx::PFmlaVbl& vbl = pfmla_vbl(*pc.wvbls[i]);
      if (!pc_symm.wvbl_symms[i]->puppet_ck()) {
        shadow_guard |= (vbl != act.assign(i));
      }
    }
    xn &= shadow_guard;
  }

  for (uint i = 0; i < pc.rvbls.sz(); ++i) {
    const Cx::PFmlaVbl& vbl = pfmla_vbl(*pc.rvbls[i]);
    if (!pc_symm.write_flags[i] && pc_symm.rvbl_symms[i]->puppet_ck()) {
      xn &= (vbl == act.guard(i));
    }
  }

  return xn;
}

  X::Fmla
Xn::Net::represented_xns_of_pc(const Xn::ActSymm& act, uint pcidx) const
{
  uint actidx = this->action_index(act);
  const Cx::Table<uint>& reps =
    this->represented_actions[actidx];
  X::Fmla xn( false );
  for (uint i = 0; i < reps.sz(); ++i) {
    ActSymm tmp_act;
    this->action(tmp_act, reps[i]);
    xn |= this->xn_of_pc(tmp_act, pcidx);
  }
  return xn;
}

  void
Xn::Net::make_action_pfmla(X::Fmla* ret_xn, uint actidx) const
{
  Xn::ActSymm act;
  this->action(act, actidx);
  const Xn::PcSymm& pc_symm = *act.pc_symm;

  X::Fmla xn(false);
  for (uint pc_memb_idx = 0; pc_memb_idx < pc_symm.membs.sz(); ++pc_memb_idx) {
    const Xn::Pc& pc = *pc_symm.membs[pc_memb_idx];
    xn |= (pc.act_unchanged_pfmla & this->xn_of_pc(act, pc_memb_idx));
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
Xn::Net::cache_action_pfmla(uint actidx)
{
  Cx::PFmla xn;
  make_action_pfmla(&xn, actidx);

  uint rep_actidx = representative_action_index(actidx);

  if (rep_actidx == actidx) {
    act_pfmlas[actidx] = xn;
  }
  else {
    act_pfmlas[actidx] = false;
    act_pfmlas[rep_actidx] |= xn;
  }
}

  bool
candidate_actions(std::vector<uint>& candidates,
                  Cx::Table<uint>& dels,
                  Cx::Table<uint>& rejs,
                  const Xn::Sys& sys)
{
  const Xn::Net& topo = sys.topology;

  if (!sys.invariant.sat_ck()) {
    DBog0( "Invariant is empty!" );
    return false;
  }

  if (sys.invariant.tautology_ck()) {
    DBog0( "All states are invariant!" );
    if (!sys.shadow_puppet_synthesis_ck()) {
      return true;
    }
  }

  for (uint actidx = 0; actidx < topo.n_possible_acts; ++actidx) {
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
    const Xn::Pc& rep_pc = *pc_symm.membs[rep_pcidx];
    const X::Fmla& pc_xn = topo.represented_xns_of_pc(act, rep_pcidx);

    const X::Fmla& act_xn = topo.action_pfmla(actidx);
    if (!act_xn.sat_ck()) {
      add = false;
    }
    if (add) {
      add = !pc_xn.overlap_ck(pc_symm.forbid_pfmla);
      if (!add) {
        rejs << actidx;
      }
    }
    if (add) {
      if (pc_symm.permit_pfmla.sat_ck()) {
        if (!pc_xn.subseteq_ck(pc_symm.permit_pfmla)) {
          add = false;
          rejs << actidx;
        }
      }
    }

    // Check for self-loops.
    if (add) {
      bool selfloop = true;
      bool shadow_exists = false;
      for (uint j = 0; j < pc_symm.wvbl_symms.sz(); ++j) {
        if (pc_symm.wvbl_symms[j]->pure_shadow_ck()) {
          shadow_exists = true;
        }
        else {
          if (act.assign(j) != act.aguard(j)) {
            selfloop = false;
          }
        }
      }
      add = !selfloop;
      if (selfloop) {
        if (shadow_exists) {
          add = true;
        }
        else {
          rejs << actidx;
        }
      }
      if (false && selfloop) {
        OPut((DBogOF << "Action " << actidx << " is a self-loop: "), act) << '\n';
      }
    }

    if (add && !act_xn.img(sys.closed_assume).subseteq_ck(sys.closed_assume)) {
      add = false;
      rejs << actidx;
    }
    if (add && !sys.closed_assume.overlap_ck(act_xn.pre())) {
      add = false;
      dels << actidx;
    }
    // Optimization. Shadow variables can just be changed as if the invariant
    // is reached or will be reached by this action.
    if (add && !topo.smooth_puppet_vbls(act_xn.img()).overlap_ck(sys.invariant)) {
      add = false;
      dels << actidx;
    }
    // Optimization. When (future & active shadow) is specified, shadow
    // variables should only change as they do in the shadow protocol.
    if (add && sys.spec->invariant_style == Xn::FutureAndActiveShadow) {
      if (!pc_xn.overlap_ck(topo.smooth_puppet_vbls(rep_pc.shadow_xn))) {
        add = false;
        dels << actidx;
      }
    }
    if (add && sys.direct_invariant_ck()) {
      if (!act_xn.img(sys.invariant & sys.closed_assume).subseteq_ck(sys.invariant)) {
        add = false;
        rejs << actidx;
        if (false) {
          OPut((DBogOF << "Action " << actidx << " breaks closure: "), act) << '\n';
        }
      }
      else if (!(act_xn & sys.invariant & sys.closed_assume)
               .subseteq_ck(sys.shadow_pfmla | sys.shadow_self))
      {
        add = false;
        rejs << actidx;
        if (false) {
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

