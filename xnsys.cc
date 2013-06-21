
#include "xnsys.hh"

/**
 * Commit to the topology represented by the vector of processes.
 *
 * TODO this function needs to go away,
 * or at least we need to initialize on a per-process basis.
 *
 * 1. Find /nPossibleActs/ for each process.
 * 2. Construct /actUnchanged/ for each process.
 */
  void
Xn::Net::commit_initialization()
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

  init_unchanged();

  act_pfmlas.resize(ntotal);
  n_possible_acts = ntotal;
  for (uint i = 0; i < ntotal; ++i) {
    this->make_action_pfmla(i);
  }
}

/**
 * Construct /act_unchanged_pfmla/ for each process.
 */
  void
Xn::Net::init_unchanged()
{
  Cx::PFmla eq(true);
  for (uint i = 0; i < vbls.sz(); ++i) {
    const Cx::PFmlaVbl& vbl = pfmla_ctx.vbl(vbls[i].pfmla_idx);
    eq &= (vbl.img_eq(vbl));
  }

  for (uint i = 0; i < pcs.sz(); ++i) {
    Xn::Pc& pc = pcs[i];
    pc.act_unchanged_pfmla = eq;
    for (uint j = 0; j < pc.wvbls.sz(); ++j) {
      pc.act_unchanged_pfmla =
        pc.act_unchanged_pfmla.smooth(pc.wvbls[j]->pfmla_list_id);
    }
  }
}

  uint
Xn::Net::action_pcsymm_index(uint actidx) const
{
  for (uint i = 0; i < pc_symms.sz()-1; ++i) {
    if (actidx < pc_symms[i+1].act_idx_offset) {
      return i;
    }
  }
  return pc_symms.sz() - 1;
}

  void
Xn::Net::action(ActSymm& act, uint actidx) const
{
  uint pcidx = this->action_pcsymm_index(actidx);
  act.pc_symm = &pc_symms[pcidx];
  const Xn::PcSymm& pc = *act.pc_symm;

  actidx -= pc.act_idx_offset;

  act.vals.resize(pc.rvbl_symms.sz() + pc.wvbl_symms.sz());
  Cx::state_of_index (&act.vals[0], actidx, pc.doms);

}

uint Xn::Net::action_index(const Xn::ActSymm& act) const
{
  const Xn::PcSymm& pc = *act.pc_symm;
  return pc.act_idx_offset +
    Cx::index_of_state (&act.vals[0], pc.doms);

}

  ostream&
Xn::Net::oput(ostream& of,
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
Xn::Sys::commit_initialization()
{
  Xn::Net& topo = this->topology;
  topo.commit_initialization();

  this->shadow_protocol = false;
  this->shadow_self = true;

  for (uint i = 0; i < topo.vbls.sz(); ++i) {
    const Xn::Vbl& vbl = topo.vbls[i];
    if (vbl.symm->shadow) {
      topo.pfmla_ctx.add_to_vbl_list (shadow_pfmla_list_id, vbl.pfmla_idx);
      const Cx::PFmlaVbl& x = topo.pfmla_ctx.vbl(vbl.pfmla_idx);
      shadow_self &= (x.img_eq(x));
      shadow_vbls_exist = true;
    }
    else {
      topo.pfmla_ctx.add_to_vbl_list (puppet_pfmla_list_id, vbl.pfmla_idx);
    }
  }
}

/** Add an action to the protocol which runs in the legitimate states.*/
  void
Xn::Sys::add_shadow_act(const ActSymm& act)
{
  const Xn::Net& topo = this->topology;
  const Xn::PcSymm& pc_symm = *act.pc_symm;

  Cx::PFmla pf( false );

  for (uint i = 0; i < pc_symm.membs.sz(); ++i) {
    const Xn::Pc& pc = *pc_symm.membs[i];
    Cx::PFmla actpf( true );
    for (uint j = 0; j < pc.rvbls.sz(); ++j) {
      if (pc.rvbls[j]->symm->shadow) {
        const Cx::PFmlaVbl& vbl = topo.pfmla_ctx.vbl(pc.rvbls[j]->pfmla_idx);
        actpf &= (vbl == act.guard(j));
      }
    }
    for (uint j = 0; j < pc.wvbls.sz(); ++j) {
      if (pc.wvbls[j]->symm->shadow) {
        const Cx::PFmlaVbl& vbl = topo.pfmla_ctx.vbl(pc.wvbls[j]->pfmla_idx);
        actpf &= (vbl.img_eq(act.assign(j)));
      }
    }
    pf |= (pc.act_unchanged_pfmla & actpf);
  }
  this->shadow_protocol |= pf;
}

  bool
Xn::Sys::integrityCk() const
{
  bool good = true;;

  if (this->invariant.tautology_ck(false)) {
    DBog0( "Error: Invariant is empty!" );
    good = false;
  }

  if (this->shadowVblCk()) {
    if (!this->invariant.equiv_ck(this->invariant.smooth(this->puppet_pfmla_list_id))) {
      DBog0( "Error: Invariant includes puppet variables." );
      good = false;
    }
  }

  if (!(this->shadow_protocol.img(this->invariant) <= this->invariant)) {
    DBog0( "Error: Protocol is not closed in the invariant!" );
    good = false;
  }

  return good;
}

/**
 * Output an action in a valid Promela format.
 */
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
  of << " ->";
  for (uint i = 0; i < pc.wvbl_symms.sz(); ++i) {
    of << ' ' << pc.wvbl_symms[i]->name
      << "[" << pc.windices[i].expression("i") << "]"
      << "=" << act.assign(i) << ';';
  }
  return of;
}

  PF
LegitInvariant(const Xn::Sys& sys, const PF& loXnRel, const PF& hiXnRel)
{
  if (!sys.shadowVblCk())  return sys.invariant;

  const PF& smooth_self = sys.shadow_self;

  const PF& smooth_live = sys.invariant;
  const PF& smooth_protocol = sys.shadow_protocol;

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

  if (!smooth_live.equiv_ck(sys.smoothPuppetVbls(puppet_live))) {
    return PF(false);
  }

  if (!(smooth_live & smooth_protocol).equiv_ck(sys.smoothPuppetVbls(puppet_live & (puppet_protocol - smooth_self)))) {
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
  if (sys.liveLegit && !xnRel.pre().tautology_ck()) {
    return false;
  }
  if (sys.shadowVblCk()) {
    const PF& shadow_protocol = sys.smoothPuppetVbls(xnRel & invariant);
    if (!sys.shadow_protocol <= shadow_protocol) {
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

