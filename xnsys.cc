
#include "xnsys.hh"

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
        if (!pc.write_flags[j]) {
          domsz = 1;
        }
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

  act_pfmlas.resize(ntotal);
  pure_shadow_pfmlas.resize(ntotal);
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
  symm.domsz_expression = domsz;
  symm.nmembs_expression = nmembs;
  symm.pfmla_list_id = pfmla_ctx.add_vbl_list();
  symm.shadow_puppet_role = role;

  for (uint i = 0; i < nmembs; ++i) {
    Vbl* vbl = &vbls.push(Vbl(&symm, i));
    symm.membs.push(vbl);
    vbl->pfmla_idx = pfmla_ctx.add_vbl(name_of (*vbl), domsz);
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

  return &symm;
}

  PcSymm*
Net::add_processes(const String& name, uint nmembs)
{
  PcSymm& symm = pc_symms.grow1();
  symm.name = name;
  symm.nmembs_expression = nmembs;
  for (uint i = 0; i < nmembs; ++i) {
    Pc& pc = pcs.push(Pc(&symm, i));
    symm.membs.push(&pc);
    pc.act_unchanged_pfmla = this->proj_puppet(this->identity_xn);
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

  for (uint act_idx = 0; act_idx < topo.n_possible_acts; ++act_idx) {
    const Cx::PFmla& act_pfmla = topo.action_pfmla(act_idx);
    if (act_pfmla <= this->direct_pfmla && act_pfmla.sat_ck()) {
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

  Claim(topo.identity_xn.sat_ck());
  Claim(topo.identity_xn.subseteq_ck(this->shadow_self));
  Claim(topo.smooth_pure_puppet_vbls(topo.identity_xn).equiv_ck(this->shadow_self));

  if (false)
  for (uint i = 0; i < topo.pcs.sz(); ++i) {
    const Xn::Pc& pc = topo.pcs[i];
    for (uint j = 0; j < pc.rvbls.sz(); ++j) {
      if (!pc.symm->write_flags[j]) {
        DBog2( "%u %u", pc.rvbls[j]->pfmla_idx, i );
      }
    }
  }

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
  of << "/*" << pc.name << "[" << pc.idx_name << "]" << "*/ ";
  const char* delim = "";
  for (uint i = 0; i < pc.rvbl_symms.sz(); ++i) {
    if (pc.rvbl_symms[i]->pure_shadow_ck()) {
      if (!pc.write_flags[i]) {
        continue;
      }
    }
    of << delim;
    delim = " && ";
    of << pc.rvbl_symms[i]->name
      << "[" << pc.rindices[i].expression << "]"
      << "==" << act.guard(i);
  }
  of << " -->";
  for (uint i = 0; i < pc.wvbl_symms.sz(); ++i) {
    of << ' ' << pc.wvbl_symms[i]->name
      << "[" << pc.windices[i].expression << "]"
      << ":=" << act.assign(i) << ';';
  }
  return of;
}

  void
find_one_cycle(Cx::Table<Cx::PFmla>& states, const Cx::PFmla& xn, const Cx::PFmla& scc)
{
  states.clear();
  states.push( scc.pick_pre() );
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
oput_one_cycle(Cx::OFile& of, const Cx::PFmla& xn, const Cx::PFmla& scc, const Xn::Net& topo)
{
  Cx::Table<Cx::PFmla> states;
  find_one_cycle(states, xn, scc);
  of << "Cycle is:\n";
  for (uint i = 0; i < states.sz(); ++i) {
    topo.oput_pfmla(of, states[i], -1, true);
  }
  of.flush();
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

  Cx::PFmla xn(false);
  Cx::PFmla pure_shadow_pfmla(true);

  for (uint pc_memb_idx = 0; pc_memb_idx < pc_symm.membs.sz(); ++pc_memb_idx) {
    const Xn::Pc& pc = *pc_symm.membs[pc_memb_idx];
    // Local transition whose guard is over puppet variables
    // but does make an assignment to the writeable pure shadow variables.
    Cx::PFmla actpf(true);
    // Fixed states for the pure shadow variables.
    Cx::PFmla pure_shadow_pre(true);
    Cx::PFmla pure_shadow_img(true);

    for (uint i = 0; i < pc.wvbls.sz(); ++i) {
      const Cx::PFmlaVbl& vbl = pfmla_vbl(*pc.wvbls[i]);
      actpf &= (vbl == act.aguard(i));
      actpf &= (vbl.img_eq(act.assign(i)));
      if (pc_symm.wvbl_symms[i]->pure_shadow_ck()) {
        pure_shadow_pre &= (vbl == act.aguard(i));
        pure_shadow_img &= (vbl == act.assign(i));
      }
    }

    for (uint i = 0; i < pc.wvbls.sz(); ++i) {
      const Cx::PFmlaVbl& vbl = pfmla_vbl(*pc.wvbls[i]);
      if (pc_symm.wvbl_symms[i]->puppet_ck()) {
        pure_shadow_pre |= (vbl != act.aguard(i));
        pure_shadow_img |= (vbl != act.assign(i));
      }
    }

    for (uint i = 0; i < pc.rvbls.sz(); ++i) {
      const Cx::PFmlaVbl& vbl = pfmla_vbl(*pc.rvbls[i]);
      if (!pc_symm.write_flags[i] && pc_symm.rvbl_symms[i]->puppet_ck()) {
        actpf &= (vbl == act.guard(i));
        pure_shadow_pre |= (vbl != act.guard(i));
        pure_shadow_img |= (vbl != act.guard(i));
      }
    }

    xn |= (pc.act_unchanged_pfmla & actpf);
    pure_shadow_pfmla &= (pure_shadow_pre & pure_shadow_img);
  }
  Claim( pure_shadow_pfmla.sat_ck() );

  if (xn.overlap_ck(this->identity_xn)) {
    if (!pure_shadow_pfmla.tautology_ck()) {
      xn = false;
    }
  }
  act_pfmlas[actidx] = xn;
  pure_shadow_pfmlas[actidx] = pure_shadow_pfmla;
}

