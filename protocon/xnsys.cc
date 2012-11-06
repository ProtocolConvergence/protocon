
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
  for (uint i = 0; i < pcs.size(); ++i) {
    XnPc& pc = pcs[i];
    for (uint j = 0; j < pc.wvbls.size(); ++j) {
      XnVbl& xnVbl = pc.wvbls[j];
      const PFVbl* pfVbl;

      pfVbl = pfCtx.add(PFVbl(xnVbl.name, xnVbl.domsz));
      xnVbl.pfIdx = pfVbl->idx;

      pfVbl = pfCtx.add(PFVbl(xnVbl.name + "p", xnVbl.domsz));
      xnVbl.pfIdxPrimed = pfVbl->idx;
    }
  }

  pfCtx.commitInitialization();

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
    pc.nPossibleActs = n;
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

