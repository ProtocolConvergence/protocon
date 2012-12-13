
#ifndef XnSys_HH_
#define XnSys_HH_

#include "synhax.hh"
#include "pf.hh"

class XnVbl {
public:
  string name; ///< Proper name of variable, should match the name in PFCtx.
  uint domsz; ///< Size of domain.
  uint pfIdx; ///< Index of unprimed variable (in a PFCtx).
  uint pfIdxPrimed; ///< Index of the primed variable (in a PFCtx).

  XnVbl(const string& _name, uint _domsz) :
    name(_name)
    , domsz(_domsz)
  {}
};

/** Variable assignments made by a specific action.*/
class XnAct {
public:
  static const uint NMax = 10;

public:
  uint pcIdx;
  uint r0[NMax];
  uint w0[NMax];
  uint w1[NMax];

public:
  XnAct()
  {
    for (uint i = 0; i < NMax; ++i) {
      r0[i] = w0[i] = w1[i] = 0;
    }
  }
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
  /// My local action of index 0 is this global action index.
  uint actIdxOffset;

public:
  void addVbl(const XnVbl& vbl)
  {
    wvbls.push_back(vbl);
  }

  void addPriv(uint pcIdx, uint vblIdx)
  {
    pair<uint,uint>& p = Grow1(rvbls);
    p.first = pcIdx;
    p.second = vblIdx;
  }
};


/** A network of processes (topology).*/
class XnNet {
private:
  uint vVblList; // Unprimed
  uint vVblListPrimed; // Primed
  vector<PF> actionPFs; ///< Storage of action formulas.

public:
  PFCtx pfCtx;
  vector<XnPc> pcs; ///< List of the processes.

public:
  ~XnNet() {
    // These need to be destroyed before the context goes away.
    actionPFs.clear();
    pcs.clear();
  }

  void commitInitialization();

  const XnVbl& wvbl(uint pcIdx, uint vblIdx) const
  {
    return pcs[pcIdx].wvbls[vblIdx];
  }

  const XnVbl& rvbl(uint pcIdx, uint vblIdx) const
  {
    const pair<uint,uint>& p = pcs[pcIdx].rvbls[vblIdx];
    return wvbl(p.first, p.second);
  }

  const PFVbl pfVbl(uint pcIdx, uint vblIdx) const
  {
    return pfCtx.vbl(pcs[pcIdx].wvbls[vblIdx].pfIdx);
  }

  const PFVbl pfVblPrimed(uint pcIdx, uint vblIdx) const
  {
    return pfCtx.vbl(pcs[pcIdx].wvbls[vblIdx].pfIdxPrimed);
  }

  const PFVbl pfVblR(uint pcIdx, uint vblIdx) const
  {
    const pair<uint,uint>& p = pcs[pcIdx].rvbls[vblIdx];
    return pfVbl(p.first, p.second);
  }

  uint nPossibleActs() const
  {
    const XnPc& pc = pcs.back();
    return pc.actIdxOffset + pc.nPossibleActs;
  }

  uint actionPcIdx(uint actIdx) const;
  const XnAct action(uint actIdx) const;
  uint actionIndex(const XnAct& act) const;

  const PF& actionPF(uint actIdx) const
  { return actionPFs[actIdx]; }

  const PF preimage(const PF& xnRel) const
  {
    return pfCtx.smooth(xnRel, vVblListPrimed);
  }

  const PF preimage(const PF& xnRel, const PF& image) const
  {
    return preimage(xnRel &
                    pfCtx.substituteNewOld(image, vVblListPrimed, vVblList));
  }

  const PF image(const PF& xnRel) const
  {
    PF pf( pfCtx.smooth(xnRel, vVblList) );
    return pfCtx.substituteNewOld(pf, vVblList, vVblListPrimed);
  }

  const PF image(const PF& xnRel, const PF& preimage) const
  {
    return image(xnRel & preimage);
  }

  ostream& oput(ostream& of,
                const PF& pf,
                const string& pfx = "",
                const string& sfx = "") const;

private:
  void initUnchanged();
  void makeActionPF(uint actIdx);
};


/** This holds the search problem and its solution.**/
class XnSys {
public:
  XnNet topology;
  vector<uint> actions; ///< Actions we are using.
  PF invariant;
  bool synLegit; ///< Allow synthesized actions to be in legitimate states.
  bool liveLegit; ///< Ensure no deadlocks in the invariant.

private:
  map<uint,uint> niceIdcs; ///< Niceness for processes, used in search.

public:
  XnSys() : synLegit(false), liveLegit(false) {}

  void niceIdxFo(uint pcIdx, uint niceIdx) {
    niceIdcs[pcIdx] = niceIdx;
  }
  uint niceIdxOf(uint pcIdx) const {
    const uint* niceIdx = MapLookup(niceIdcs, pcIdx);
    if (!niceIdx) {
      return topology.pcs.size() + pcIdx;
    }
    return *niceIdx;
  }
};

ostream&
OPut(ostream& of, const XnAct& act, const XnNet& topo);
bool
WeakConvergenceCk(const XnSys& sys, const PF& xnRel);
bool
CycleCk(const XnSys& sys, const PF& xnRel);
PF
BackwardReachability(const PF& xnRel, const PF& pf, const XnNet& topo);

#endif

