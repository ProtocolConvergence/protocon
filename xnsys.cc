
#include "xnsys.hh"
#include "set.hh"

/**
 * Commit to the topology represented by the vector of processes.
 * 1. Create the PFCtx with unprimed and primed variables using
 *    proper names and domain sizes.
 *    In the process, propagate the following data to members:
 *     - pfIdx to variable
 *     - pfIdxPrimed to variable
 * 2. Find /nPossibleActs/ for each process.
 * 3. Construct /actUnchanged/ for each process.
 */
  void
XnNet::commitInitialization()
{
  for (uint i = 0; i < pcs.size(); ++i) {
    XnPc& pc = pcs[i];
    for (uint j = 0; j < pc.wvbls.size(); ++j) {
      XnVbl& xnVbl = pc.wvbls[j];

      xnVbl.pfIdx = pfCtx.addVbl (xnVbl.name, xnVbl.domsz);
      pfCtx.addToVblList (vVblList, xnVbl.pfIdx);

      xnVbl.pfIdxPrimed = pfCtx.addVbl (xnVbl.name + "p", xnVbl.domsz);
      pfCtx.addToVblList(vVblListPrimed, xnVbl.pfIdxPrimed);
    }
  }

  pfCtx.commitInitialization();

  uint nTotalActs = 0;
  for (uint i = 0; i < pcs.size(); ++i) {
    XnPc& pc = pcs[i];
    uint n = 1;

    for (uint j = 0; j < pc.wvbls.size(); ++j) {
      uint domsz = pc.wvbls[j].domsz;
      n *= domsz * domsz;
    }
    for (uint j = 0; j < pc.rvbls.size(); ++j) {
      pair<uint,uint> p = pc.rvbls[j];
      uint domsz = pcs[p.first].wvbls[p.second].domsz;
      n *= domsz;
    }

    pc.actIdxOffset = nTotalActs;
    pc.nPossibleActs = n;
    nTotalActs += n;
  }

  initUnchanged();

  actionPFs.resize(nTotalActs);
  for (uint actId = 0; actId < nTotalActs; ++actId) {
    this->makeActionPF(actId);
  }
}

/**
 * Construct /actUnchanged/ for each process.
 */
  void
XnNet::initUnchanged()
{
  for (uint i = 0; i < pcs.size(); ++i) {
    pcs[i].actUnchanged = true;
  }
  for (uint i = 0; i < pcs.size(); ++i) {
    XnPc& pc = pcs[i];
    PF eq(true);
    for (uint j = 0; j < pc.wvbls.size(); ++j) {
      const XnVbl& xnVbl = pc.wvbls[j];
      eq &= (pfCtx.vbl(xnVbl.pfIdx) == pfCtx.vbl(xnVbl.pfIdxPrimed));
    }
    for (uint j = 0; j < pcs.size(); ++j) {
      if (i != j) {
        pcs[j].actUnchanged &= eq;
      }
    }
  }
}

  uint
XnNet::actionPcIdx(uint actIdx) const
{
  for (uint i = 0; i < pcs.size()-1; ++i) {
    if (actIdx < pcs[i+1].actIdxOffset) {
      return i;
    }
  }
  return pcs.size() - 1;
}

  const XnAct
XnNet::action(uint actIdx) const
{
  XnAct act;
  act.pcIdx = this->actionPcIdx(actIdx);

  const XnPc& pc = pcs[act.pcIdx];
  uint nPossibleActs = pc.nPossibleActs;
  actIdx -= pc.actIdxOffset;;

  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    nPossibleActs /= wvbl(act.pcIdx, i).domsz;
    act.w1[i] = actIdx / nPossibleActs;
    actIdx = actIdx % nPossibleActs;
  }
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    nPossibleActs /= wvbl(act.pcIdx, i).domsz;
    act.w0[i] = actIdx / nPossibleActs;
    actIdx = actIdx % nPossibleActs;
  }
  for (uint i = 0; i < pc.rvbls.size(); ++i) {
    nPossibleActs /= rvbl(act.pcIdx, i).domsz;
    act.r0[i] = actIdx / nPossibleActs;
    actIdx = actIdx % nPossibleActs;
  }
  return act;
}

uint XnNet::actionIndex(const XnAct& act) const
{
  const XnPc& pc = pcs[act.pcIdx];
  uint actIdx = 0;
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    actIdx *= wvbl(act.pcIdx, i).domsz;
    actIdx += act.w1[i];
  }
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    actIdx *= wvbl(act.pcIdx, i).domsz;
    actIdx += act.w0[i];
  }
  for (uint i = 0; i < pc.rvbls.size(); ++i) {
    actIdx *= rvbl(act.pcIdx, i).domsz;
    actIdx += act.r0[i];
  }
  return actIdx + pc.actIdxOffset;
}

  ostream&
XnNet::oput(ostream& of,
            const PF& pf,
            const string& pfx,
            const string& sfx) const
{
  return this->pfCtx.oput(of, pf, this->vVblList, pfx, sfx);
}


  void
XnSys::commitInitialization()
{
  XnNet& topo = this->topology;
  topo.commitInitialization();

  for (uint i = 0; i < this->aux_vbls.size(); ++i) {
    const XnPc& pc = topo.pcs[this->aux_vbls[i].first];
    const XnVbl& vbl = pc.wvbls[this->aux_vbls[i].second];
    topo.pfCtx.addToVblList(this->vAuxVblListId, vbl.pfIdx);
    topo.pfCtx.addToVblList(this->vAuxVblListId, vbl.pfIdxPrimed);
  }

  this->legit_protocol = false;

  this->legit_self = true;
  Set< pair<uint,uint> > aux( this->aux_vbls );
  for (uint i = 0; i < topo.pcs.size(); ++i) {
    const XnPc& pc = topo.pcs[i];
    for (uint j = 0; j < pc.wvbls.size(); ++j) {
      pair<uint,uint> p( i, j );
      if (!aux.elemCk(p)) {
        this->legit_self &= (topo.pfVbl(i, j) == topo.pfVblPrimed(i, j));
      }
    }
  }
}

/** Add an action to the protocol which runs in the legitimate states.*/
  void
XnSys::addLegitAct(const XnAct& act)
{
  const XnNet& topo = this->topology;
  uint actId = topo.actionIndex(act);
  const PF& actPF = topo.actionPF(actId);
  this->legit_protocol |= actPF.smooth(this->vAuxVblListId);
}

  bool
XnSys::integrityCk() const
{
  const XnNet& topo = this->topology;
  bool good = true;;

  if (this->invariant.tautologyCk(false)) {
    DBog0( "Error: Invariant is empty!" );
    good = false;
  }

  if (this->auxVblCk()) {
    if (!this->invariant.equivCk(this->invariant.smooth(this->vAuxVblListId))) {
      DBog0( "Error: Invariant includes auxiliary variables." );
      good = false;
    }
  }

  if (!(topo.image(this->legit_protocol, this->invariant) <= this->invariant)) {
    DBog0( "Error: Protocol is not closed in the invariant!" );
    good = false;
  }

  return good;
}

/**
 * Output an action in a valid Promela format.
 */
  ostream&
OPut(ostream& of, const XnAct& act, const XnNet& topo)
{
  const XnPc& pc = topo.pcs[act.pcIdx];
  of << "/*P" << act.pcIdx << "*/ ";
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    if (i != 0)  of << " && ";
    of << topo.wvbl(act.pcIdx, i).name << "==" << act.w0[i];
  }
  for (uint i = 0; i < pc.rvbls.size(); ++i) {
    of << " && ";
    of << topo.rvbl(act.pcIdx, i).name << "==" << act.r0[i];
  }
  of << " ->";
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    of << ' ' << topo.wvbl(act.pcIdx, i).name << "=" << act.w1[i] << ';';
  }
  return of;
}

  PF
ClosedSubset(const PF& xnRel, const PF& invariant, const XnNet& topo)
{
  return invariant - BackwardReachability(xnRel, ~invariant, topo);
}

  PF
LegitInvariant(const XnSys& sys, const PF& loXnRel, const PF& hiXnRel)
{
  const XnNet& topo = sys.topology;
  if (!sys.auxVblCk())  return sys.invariant;

  const PF& smooth_self = sys.legit_self;

  const PF& smooth_live = sys.invariant;
  const PF& smooth_protocol = sys.legit_protocol;

  PF aux_live = smooth_live - topo.preimage(loXnRel - smooth_protocol - smooth_self);
  aux_live = ClosedSubset(loXnRel, aux_live, sys.topology);
  const PF& aux_protocol = hiXnRel & (smooth_protocol | smooth_self);

  if (CycleCk(topo, loXnRel & smooth_self, aux_live)) {
    return PF(false);
  }

  const PF& smooth_beg = smooth_live - topo.image(smooth_protocol, smooth_live);
  const PF& smooth_end = smooth_live - topo.preimage(smooth_protocol, smooth_live);

  while (true)
  {
    const PF old_live = aux_live;

    aux_live &= (smooth_beg & aux_live) | topo.image(aux_protocol, aux_live);
    aux_live &= (smooth_end & aux_live) | topo.preimage(aux_protocol, aux_live);

    if (old_live.equivCk(aux_live)) {
      break;
    }
  }

  if (!smooth_live.equivCk(sys.smoothAux(aux_live))) {
    return PF(false);
  }

  if (!(smooth_live & smooth_protocol).equivCk(sys.smoothAux(aux_live & (aux_protocol - smooth_self)))) {
    return PF(false);
  }
  return aux_live;
}

/**
 * Check for weak convergence to the invariant.
 */
  bool
WeakConvergenceCk(const XnSys& sys, const PF& xnRel, const PF& invariant)
{
  const XnNet& topo = sys.topology;
  if (sys.liveLegit && !topo.preimage(xnRel).tautologyCk()) {
    return false;
  }
  if (sys.auxVblCk()) {
    const PF& legit_protocol = sys.smoothAux(xnRel & invariant);
    if (!sys.legit_protocol <= legit_protocol) {
      return false;
    }
  }

  PF span0( invariant );
  while (!span0.tautologyCk(true)) {
    PF span1( span0 | topo.preimage(xnRel, span0) );
    if (span1.equivCk(span0))  return false;
    span0 = span1;
  }
  return true;
}

  bool
WeakConvergenceCk(const XnSys& sys, const PF& xnRel)
{
  return WeakConvergenceCk(sys, xnRel, sys.invariant);
}

/**
 * Check for cycles within some state predicate.
 */
  bool
CycleCk(PF* scc, const XnNet& topo, const PF& xnRel, const PF& pf)
{
  PF span0( true );

  while (true) {
    const PF& span1 = topo.image(xnRel, span0);

    if (!pf.overlapCk(span1))  return false;
    if (span0.equivCk(span1))  break;

    span0 = span1;
  }

  if (scc) {
    *scc = span0;
  }
  return true;
}

/**
 * Check for cycles within some state predicate.
 */
  bool
CycleCk(const XnNet& topo, const PF& xnRel, const PF& pf)
{
  return CycleCk(0, topo, xnRel, pf);
}


/**
 * Perform backwards reachability.
 * \param xnRel  Transition function.
 * \param pf  Initial states.
 * \param topo  Topology of the system.
 */
  PF
BackwardReachability(const PF& xnRel, const PF& pf, const XnNet& topo)
{
  PF visitPF( pf );
  PF layerPF( topo.preimage(xnRel, pf) - visitPF );
  while (!layerPF.tautologyCk(false)) {
    visitPF |= layerPF;
    layerPF = topo.preimage(xnRel, layerPF) - visitPF;
  }
  return visitPF;
}

/**
 * Create a persistent PF for this action.
 * \sa commitInitialization()
 **/
  void
XnNet::makeActionPF(uint actIdx)
{
  const XnAct act = action(actIdx);
  const XnPc& pc = pcs[act.pcIdx];
  PF pf(true);
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    pf &= (pfVbl      (act.pcIdx, i) == act.w0[i]);
    pf &= (pfVblPrimed(act.pcIdx, i) == act.w1[i]);
  }
  for (uint i = 0; i < pc.rvbls.size(); ++i) {
    pf &= (pfVblR(act.pcIdx, i) == act.r0[i]);
  }
  pf &= pc.actUnchanged;

  actionPFs[actIdx] = pf;
}

