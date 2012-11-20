
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
}

/**
 * Construct /actUnchanged/ for each process.
 */
  void
XnNet::initUnchanged()
{
  for (uint i = 0; i < pcs.size(); ++i) {
    XnPc& pc = pcs[i];
    PF eq;
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

const XnAct XnNet::action(uint actIdx) const
{
  XnAct act;
  act.pcIdx = pcs.size() - 1;
  for (uint i = 0; i < pcs.size()-1; ++i) {
    if (actIdx < pcs[i+1].actIdxOffset) {
      act.pcIdx = i;
      break;
    }
  }

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
  return actIdx;
}

const PF XnNet::actionPF(uint actIdx) const
{
  const XnAct act = action(actIdx);
  const XnPc& pc = pcs[act.pcIdx];
  PF pf;
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    pf &= (pfVbl      (act.pcIdx, i) == act.w0[i]);
    pf &= (pfVblPrimed(act.pcIdx, i) == act.w1[i]);
  }
  for (uint i = 0; i < pc.rvbls.size(); ++i) {
    pf &= (pfVblR(act.pcIdx, i) == act.r0[i]);
  }
  pf &= pc.actUnchanged;
  return pf;
}
