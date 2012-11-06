
#ifndef XnSys_HH_
#define XnSys_HH_

#include "synhax.hh"
#include "pf.hh"

class XnVbl {
public:
  string name; //< Proper name of variable, should match the name in PFCtx.
  uint domsz; ///< Size of domain.
  uint pfIdx; ///< Index of unprimed variable (in a PFCtx).
  uint pfIdxPrimed; ///< Index of the primed variable (in a PFCtx).

  XnVbl(const string& _name, uint _domsz) :
    name(_name)
    , domsz(_domsz)
  {}
};

/** A process.*/
class XnPc {
public:
  vector<XnVbl> wvbls; ///< Variables this process owns.

  /** List of readable variables as
   * (process index, local variable index) pairs.
   */
  vector< pair<uint,uint> > rvbls;

  /** Conjunct this with actions of the process to ensure only
   * the process's variables change when it acts. 
   */
  PF actUnchanged;

  /// Number of possible local transitions based on topology.
  uint nPossibleActs;

public:
  void addVbl(const XnVbl& vbl)
  {
    wvbls.push_back(vbl);
  }

  void addPriv(uint pcIdx, uint vblIdx)
  {
    pair<uint,uint>& p = Grow1(rvbls);
    p.first = pcIdx;
    p.first = vblIdx;
  }
};

/** A network of processes (topology).*/
class XnNet {
public:
  PFCtx pfCtx;
  vector<XnPc> pcs; ///< List of the processes.

public:
  // TODO - Need some "nice" way to add processes
  // and hook up their read restrictions.

  void commitInitialization();

  const PFVbl pfVbl(uint pcIdx, uint vblIdx)
  {
    return pfCtx.vbl(pcs[pcIdx].wvbls[vblIdx].pfIdx);
  }

  const PFVbl pfVblPrimed(uint pcIdx, uint vblIdx)
  {
    return pfCtx.vbl(pcs[pcIdx].wvbls[vblIdx].pfIdxPrimed);
  }

  //const PF image(const PF& states);
  //const PF preimage(const PF& states);

private:
  void initUnchanged();
};

/** A lightweight class to hold actual transitions?**/
class XnSys {
public:
  XnNet* topology;
  PF actions;
  //PF invariant;

public:
};

#endif

