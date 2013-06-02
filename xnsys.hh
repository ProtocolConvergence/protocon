
#ifndef XnSys_HH_
#define XnSys_HH_

#include "cx/set.hh"
#include "cx/synhax.hh"
#include "cx/table.hh"
#include "pfmla.hh"
#include "tuple.hh"

#if 0
namespace Xn {
typedef std::string String;

class VblSymm;
class Vbl;
class Topology;


class NatMap {
private:
  Cx::Table< int > membs;
  String param_name;
  String expression;
public:

  uint index(uint i, uint m) const {
    int x = membs[i];
    uint y = 0;
    if (x < 0) {
      y = (m - ((uint) (- x) % m));
    }
    else {
      y = (uint) x % m;
    }
    return y;
  }
};

class VblSymm {
private:
  bool single;
  String name;
  Cx::Table( Vbl* ) membs;
  uint domsz;
public:
};

class Vbl {
private:
  VblSymm* symm;
};

class PcSymm {
private:
  String name;
  Cx::Table< Pc* > membs;
  Cx::Table< VblSymm* > rvbls;
  Cx::Table< VblSymm* > wvbls;
  Cx::Table< NatMap > rindices;
  Cx::Table< NatMap > windices;
public:
};

class Pc {
private:
  Cx::Table< Vbl* > rvbls;
  Cx::Table< Vbl* > wvbls;
  PcSymm* symm;
public:
};

class Net {
private:
  LgTable< VblSymm > vblsymms;
  LgTable< Vbl > vbls;
  LgTable< Pc > pcs;
  LgTable< PcSymm > pcsymms;
public:
};

}

#endif

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
  vector< Cx::Tuple<uint,2> > rvbls;

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
    Cx::Tuple<uint,2>& p = Grow1(rvbls);
    p[0] = pcIdx;
    p[1] = vblIdx;
  }
};

/** A network of processes (topology).*/
class XnNet {
private:
  uint vVblList; // Unprimed
  uint vVblListPrimed; // Primed
  vector<PF> actionPFs; ///< Storage of action formulas.
  //Cx::Table< ActSet > actsets;

public:
  PFCtx pfCtx;
  vector<XnPc> pcs; ///< List of the processes.

public:

  XnNet()
  {
    vVblList = pfCtx.addVblList();
    vVblListPrimed = pfCtx.addVblList();
  }

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
    const Cx::Tuple<uint,2>& p = pcs[pcIdx].rvbls[vblIdx];
    return wvbl(p[0], p[1]);
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
    const Cx::Tuple<uint,2>& p = pcs[pcIdx].rvbls[vblIdx];
    return pfVbl(p[0], p[1]);
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

  const PF pre(const PF& xnRel) const
  {
    return xnRel.smooth(vVblListPrimed);
  }
  const PF preimage(const PF& xnRel) const
  { return pre(xnRel); }

  const PF pre(const PF& xnRel, const PF& image) const
  {
    return pre(xnRel & image.substituteNewOld(vVblListPrimed, vVblList));
  }
  const PF preimage(const PF& xnRel, const PF& image) const
  { return pre(xnRel, image); }

  const PF img(const PF& xnRel) const
  {
    PF pf( xnRel.smooth(vVblList) );
    return pf.substituteNewOld(vVblList, vVblListPrimed);
  }

  const PF image(const PF& xnRel) const
  { return img(xnRel); }

  const PF img(const PF& xnRel, const PF& preimage) const
  {
    return image(xnRel & preimage);
  }
  const PF image(const PF& xnRel, const PF& preimage) const
  { return img(xnRel, preimage); }

  ostream& oput(ostream& of,
                const PF& pf,
                const string& pfx = "",
                const string& sfx = "") const;

private:
  void initUnchanged();
  void makeActionPF(uint actIdx);
};

#if 0
class XnSet {
private:
  XnNet* topology;
public:
  const PF img() const {
  }
};
#endif

class ActSet {
public:
  Set<uint> ids; ///< Action ids which make up this set.
  PF pfmla; ///< Formula representing the transitions.

  /// Indices of other action sets which this one conflicts with.
  Set<uint> conflicts;
  PF conflict_pfmla; ///< Formula representing the conflicting actions.
};


/** This holds the search problem and its solution.**/
class XnSys {
public:
  XnNet topology;
  vector<uint> actions; ///< Force use of these actions.

  /// Invariant to which we should converge.
  PF invariant;
  /// Variables defining the original protocol.
  Set< Cx::Tuple<uint,2> > shadow_vbls;
  /// Variables used to add convergence.
  Set< Cx::Tuple<uint,2> > puppet_vbls;
  /// Transition relation within the invariant.
  PF shadow_protocol;
  /// Self-loops in the invariant.
  PF shadow_self;

  bool synLegit; ///< Allow synthesized actions to be in legitimate states.
  bool liveLegit; ///< Ensure no deadlocks in the invariant.

private:
  map<uint,uint> niceIdcs; ///< Niceness for processes, used in search.
  uint vShadowVblListId;
  uint vPuppetVblListId;

public:
  XnSys() :
    synLegit(false)
    , liveLegit(false)
  {
    this->vShadowVblListId = this->topology.pfCtx.addVblList();
    this->vPuppetVblListId = this->topology.pfCtx.addVblList();
  }


  void markShadowVbl(uint pcIdx, uint vblIdx) {
    shadow_vbls |= Cx::Tuple<uint,2>( pcIdx, vblIdx );
  }
  void commitInitialization();

  void addShadowAct(const Cx::PFmla& pf, const Set< Cx::Tuple<uint,2> >& vbls);

  bool integrityCk() const;

  bool shadowVblCk() const {
    return shadow_vbls.size() > 0;
  }
  PF smoothShadowVbls(const PF& pf) const {
    return pf.smooth(vShadowVblListId);
  }
  PF smoothPuppetVbls(const PF& pf) const {
    return pf.smooth(vPuppetVblListId);
  }

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
PF
ClosedSubset(const PF& xnRel, const PF& invariant, const XnNet& topo);
PF
LegitInvariant(const XnSys& sys, const PF& loXnRel, const PF& hiXnRel);
bool
WeakConvergenceCk(const XnSys& sys, const PF& xnRel, const PF& invariant);
bool
WeakConvergenceCk(const XnSys& sys, const PF& xnRel);
bool
CycleCk(PF* scc, const XnNet& topo, const PF& xnRel, const PF& pf);
bool
CycleCk(const XnNet& topo, const PF& xnRel, const PF& pf);
PF
BackwardReachability(const PF& xnRel, const PF& pf, const XnNet& topo);

#endif

