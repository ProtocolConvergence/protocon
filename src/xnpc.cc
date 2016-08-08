
#include "xnpc.hh"

#include "namespace.hh"
namespace Xn {

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
PcSymm::init_representative()
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
      representative_pcidx = i;
      return true;
    }
  }
  return false;
}

  bool
PcSymm::representative(uint* ret_pcidx) const
{
  if (representative_pcidx < membs.sz()) {
    *ret_pcidx = representative_pcidx;
    return true;
  }
  return false;
}

static
  void
swap_pre_img (uint* vals, const Xn::PcSymm& pc_symm)
{
  uint off = pc_symm.rvbl_symms.sz();
  const Table<uint>& wmap = pc_symm.spec->wmap;
  for (uint i = 0; i < wmap.sz(); ++i) {
    uint* pre_x = &vals[wmap[i]];
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
Pc::actions(Table<uint>& ret_actions, PFmlaCtx& ctx) const
{
  const Pc& pc = *this;
  const PcSymm& pc_symm = *pc.symm;

  Table<uint> pfmla_rvbl_idcs;
  for (uint i = 0; i < pc.rvbls.sz(); ++i) {
    pfmla_rvbl_idcs.push(pc.rvbls[i]->pfmla_idx);
  }
  Table<uint> pfmla_wvbl_idcs;
  for (uint i = 0; i < pc.wvbls.sz(); ++i) {
    pfmla_wvbl_idcs.push(pc.wvbls[i]->pfmla_idx);
  }

  X::Fmla xn( pc.puppet_xn & pc.closed_assume );

  ActSymm act;
  act.vals.grow(pc.rvbls.sz() + pc.wvbls.sz());

  while (xn.sat_ck()) {
    uint* pre_state = &act.vals[0];
    xn.state(pre_state, pfmla_rvbl_idcs);

    P::Fmla pre_pf = ctx.pfmla_of_state(pre_state, pfmla_rvbl_idcs);
    for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
      const Xn::VblSymm& vbl_symm = *pc_symm.rvbl_symms[i];
      if (!vbl_symm.pure_shadow_ck())
        continue;
      const PFmlaVbl& v = ctx.vbl(pc.rvbls[i]->pfmla_idx);
      pre_pf = pre_pf.smooth(v);
      pre_state[i] = 0;
    }

    P::Fmla img_pf = xn.img(pre_pf);
    for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
      if (pc_symm.spec->access[i].random_write_ck()) {
        const PFmlaVbl& v = ctx.vbl(pc.rvbls[i]->pfmla_idx);
        img_pf = img_pf.smooth(v) & (v == 0);
      }
    }

    while (img_pf.sat_ck()) {
      uint* img_state = &act.vals[pc.rvbls.sz()];
      img_pf.state(img_state, pfmla_wvbl_idcs);
      P::Fmla tmp_pf = ctx.pfmla_of_state(img_state, pfmla_wvbl_idcs);

      for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
        const Xn::VblSymm& vbl_symm = *pc_symm.wvbl_symms[i];
        if (!vbl_symm.pure_shadow_ck())
          continue;
        const PFmlaVbl& v = ctx.vbl(pc.wvbls[i]->pfmla_idx);
        const P::Fmla& pf = tmp_pf.smooth(v);
        if (pf.subseteq_ck(img_pf)) {
          tmp_pf = pf;
          img_state[i] = vbl_symm.domsz;
        }
      }

      uint actidx = pc_symm.act_idx_offset +
        Cx::index_of_state (&act.vals[0], pc_symm.doms);
      ret_actions.push(actidx);
      img_pf -= tmp_pf;
    }
    xn -= pre_pf;
  }
}

  void
PcSymm::actions(Table<uint>& ret_actions, PFmlaCtx& ctx) const
{
  uint pcidx = 0;

#if 1
  Table<uint> pcidcs;
  if (this->representative(&pcidx)) {
    pcidcs.push(pcidx);
  }
  else {
    for (uint i = 0; i < membs.sz(); ++i) {
      pcidcs.push(i);
    }
    // TODO: Can't debug. Race condition in parallel section.
    //DBog0("System may not represent all actions!");
  }

  Set<uint> action_set;
  for (uint i = 0; i < pcidcs.sz(); ++i) {
    Table<uint> actions;
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
  X::Fmla xn = pc.direct_pfmla;
  while (xn.sat_ck()) {
    uint* pre_state = &act.vals[0];
    xn.state(pre_state, pfmla_rvbl_idcs);
    P::Fmla pre_pf = ctx.pfmla_of_state(pre_state, pfmla_rvbl_idcs);
    P::Fmla img_pf = pfmla.img(pre_pf);

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

}
END_NAMESPACE

