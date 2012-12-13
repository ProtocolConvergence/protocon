
#include "xnsys.hh"

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
  vVblList = pfCtx.addVblList();
  vVblListPrimed = pfCtx.addVblList();

  for (uint i = 0; i < pcs.size(); ++i) {
    XnPc& pc = pcs[i];
    for (uint j = 0; j < pc.wvbls.size(); ++j) {
      XnVbl& xnVbl = pc.wvbls[j];
      const PFVbl* pfVbl;

      pfVbl = pfCtx.add(PFVbl(xnVbl.name, xnVbl.domsz));
      xnVbl.pfIdx = pfVbl->idx;
      pfCtx.addToVblList(vVblList, pfVbl->idx);

      pfVbl = pfCtx.add(PFVbl(xnVbl.name + "p", xnVbl.domsz));
      xnVbl.pfIdxPrimed = pfVbl->idx;
      pfCtx.addToVblList(vVblListPrimed, pfVbl->idx);
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

/**
 * Check for weak convergence to the invariant.
 */
  bool
WeakConvergenceCk(const XnSys& sys, const PF& xnRel)
{
  const XnNet& topo = sys.topology;
  if (sys.liveLegit && !(sys.invariant <= topo.preimage(xnRel))) {
    return false;
  }
  PF span0( sys.invariant );
  while (!span0.tautologyCk(true)) {
    PF span1( span0 | topo.preimage(xnRel, span0) );
    if (span1.equivCk(span0))  return false;
    span0 = span1;
  }
  return true;
}

/**
 * Check for cycles outside of the invariant.
 */
  bool
CycleCk(const XnSys& sys, const PF& xnRel)
{
  PF span0( ~sys.invariant );

  const XnNet& topo = sys.topology;
  while (true) {
    PF span1( span0 );
    //span0 -= span0 - sys.image(xnRel, span0);
    span0 &= topo.preimage(xnRel, span0);

    if (span0.equivCk(span1))  break;
  }

  return !span0.tautologyCk(false);
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

