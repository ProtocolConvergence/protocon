
#ifndef XnSys_HH_
#define XnSys_HH_

#include "cx/set.hh"
#include "cx/synhax.hh"
#include "cx/table.hh"
#include "cx/alphatab.hh"
#include "cx/map.hh"
#include "pfmla.hh"
#include "tuple.hh"

namespace Xn {
using Cx::String;

class NatMap;
class Vbl;
class VblSymm;
class Pc;
class PcSymm;
class ActSymm;
class Net;

class NatMap {
public:
  Cx::Table< int > membs;
  /// Between chunks is the index parameter.
  Cx::Table< String > expression_chunks;

  NatMap(uint nmembs) {
    for (uint i = 0; i < nmembs; ++i) {
      membs.push(i);
    }
    expression_chunks.push("");
  }

  int eval(uint i) const {
    Claim2( i ,<, membs.sz() );
    return membs[i];
  }

  uint index(uint i, uint m) const {
    return umod_int (eval (i), m);
  }

  String expression(const String& idxparam) const
  {
    String s = expression_chunks[0];
    for (uint i = 1; i < expression_chunks.sz(); ++i) {
      s += idxparam;
      s += expression_chunks[i];;
    }
    return s;
  }
};

class Vbl {
public:
  const VblSymm* symm;
  uint symm_idx;
  uint pfmla_idx; ///< Index of the variable (in a PmlaFCtx).
  uint pfmla_list_id;

  Vbl(VblSymm* symmetry, uint index)
    : symm(symmetry)
    , symm_idx(index)
  {}
};

class VblSymm {
public:
  uint domsz;
  String name;
  Cx::Table< Vbl* > membs;
  uint pfmla_list_id;
  bool shadow;

  VblSymm()
    : shadow(false)
  {}
};

inline String name_of(const Vbl& vbl) {
  return vbl.symm->name + "[" + vbl.symm_idx + "]";
}

class Pc {
public:
  const PcSymm* symm;
  uint symm_idx;
  /// The rvbls should include wvbls.
  Cx::Table< const Vbl* > rvbls;
  Cx::Table< const Vbl* > wvbls;
  Cx::PFmla act_unchanged_pfmla;

  Pc(PcSymm* symmetry, uint index)
    : symm(symmetry)
    , symm_idx(index)
  {}
};

class ActSymm {
public:
  const PcSymm* pc_symm;
  Cx::Table< uint > vals;

  uint guard(uint vbl_idx) const;
  uint assign(uint vbl_idx) const;
  uint aguard(uint vbl_idx) const;
};

class PcSymm {
public:
  String name;
  Cx::Table< Pc* > membs;
  /// The rvbls should include wvbls.
  Cx::Table< const VblSymm* > rvbl_symms;
  Cx::Table< const VblSymm* > wvbl_symms;
  Cx::Table< uint > wmap;
  Cx::Table< NatMap > rindices;
  Cx::Table< NatMap > windices;
  /// Domains of readable variables.
  Cx::Table< uint > doms;

  uint act_idx_offset;
  uint n_possible_acts;

  String vbl_name(uint i, const String& idxparam = "i") const {
    const String& name = rvbl_symms[i]->name;
    return name + "(" + rindices[i].expression(idxparam) + ")";
  }
};

inline uint ActSymm::guard(uint vbl_idx) const
{ return this->vals[vbl_idx]; }
inline uint ActSymm::assign(uint vbl_idx) const
{ return this->vals[this->pc_symm->rvbl_symms.sz() + vbl_idx]; }
inline uint ActSymm::aguard(uint vbl_idx) const
{ return this->guard(this->pc_symm->wmap[vbl_idx]); }

class Net {
public:
  Cx::PFmlaCtx pfmla_ctx;
  Cx::LgTable< Vbl > vbls;
  Cx::LgTable< VblSymm > vbl_symms;
  Cx::LgTable< Pc > pcs;
  Cx::LgTable< PcSymm > pc_symms;

  Cx::Table< Cx::PFmla > act_pfmlas;
  uint n_possible_acts;

public:
  void commit_initialization();

  VblSymm* add_variables(const String& name, uint nmembs, uint domsz)
  {
    VblSymm& symm = vbl_symms.grow1();
    symm.name = name;
    symm.domsz = domsz;
    symm.pfmla_list_id = pfmla_ctx.add_vbl_list();

    for (uint i = 0; i < nmembs; ++i) {
      Vbl* vbl = &vbls.push(Vbl(&symm, i));
      symm.membs.push(vbl);
      vbl->pfmla_idx = pfmla_ctx.add_vbl(name_of (*vbl), domsz);
      vbl->pfmla_list_id = pfmla_ctx.add_vbl_list();
      pfmla_ctx.add_to_vbl_list(vbl->pfmla_list_id, vbl->pfmla_idx);
      pfmla_ctx.add_to_vbl_list(symm.pfmla_list_id, vbl->pfmla_idx);
    }
    return &symm;
  }

  PcSymm* add_processes(const String& name, uint nmembs)
  {
    PcSymm& symm = pc_symms.grow1();
    symm.name = name;
    for (uint i = 0; i < nmembs; ++i) {
      symm.membs.push( &pcs.push( Pc(&symm, i) ) );
    }
    return &symm;
  }

  void add_read_access (PcSymm* pc_symm, const VblSymm* vbl_symm,
                        const NatMap& indices)
  {
    pc_symm->rvbl_symms.push(vbl_symm);
    pc_symm->rindices.push(indices);
    for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
      const Vbl* vbl = vbl_symm->membs[indices.index(i, vbl_symm->membs.sz())];
      pc_symm->membs[i]->rvbls.push(vbl);
    }
  }

  void add_write_access (PcSymm* pc_symm, const VblSymm* vbl_symm,
                         const NatMap& indices)
  {
    add_read_access (pc_symm, vbl_symm, indices);
    pc_symm->wvbl_symms.push(vbl_symm);
    pc_symm->wmap.push(pc_symm->rvbl_symms.sz() - 1);
    pc_symm->windices.push(indices);
    for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
      const Vbl* vbl = vbl_symm->membs[indices.index(i, vbl_symm->membs.sz())];
      pc_symm->membs[i]->wvbls.push(vbl);
    }
  }

  uint action_pcsymm_index(uint actidx) const;
  void action(ActSymm& act, uint actidx) const;
  uint action_index(const ActSymm& act) const;
  const Cx::PFmla& action_pfmla(uint i) const {
    return act_pfmlas[i];
  }

  Cx::PFmlaVbl pfmla_vbl(uint i) {
    return this->pfmla_ctx.vbl(this->vbls[i].pfmla_idx);
  }
  Cx::PFmlaVbl pfmla_vbl(const Vbl& x) {
    return this->pfmla_ctx.vbl(x.pfmla_idx);
  }

  ostream& oput(ostream& of,
                const Cx::PFmla& pf,
                const String& pfx,
                const String& sfx) const;

private:
  void init_unchanged();
  void make_action_pfmla(uint actid);
};

/** This holds the search problem and its solution.**/
class Sys {
public:
  Xn::Net topology;
  //XnNet topology;
  vector<uint> actions; ///< Force use of these actions.

  /// Invariant to which we should converge.
  Cx::PFmla invariant;
  /// Variables defining the original protocol.
  //Set< Cx::Tuple<uint,2> > shadow_vbls;
  /// Variables used to add convergence.
  //Set< Cx::Tuple<uint,2> > puppet_vbls;
  /// Transition relation within the invariant.
  bool shadow_vbls_exist;
  Cx::PFmla shadow_protocol;
  /// Self-loops in the invariant.
  Cx::PFmla shadow_self;

  bool synLegit; ///< Allow synthesized actions to be in legitimate states.
  bool liveLegit; ///< Ensure no deadlocks in the invariant.

private:
  Map<uint,uint> niceIdcs; ///< Niceness for process symmetries, used in search.
  uint shadow_pfmla_list_id;
  uint puppet_pfmla_list_id;

public:
  Sys()
    : shadow_vbls_exist(false)
    , synLegit(false)
    , liveLegit(false)
  {
    this->shadow_pfmla_list_id = this->topology.pfmla_ctx.add_vbl_list();
    this->puppet_pfmla_list_id = this->topology.pfmla_ctx.add_vbl_list();
  }


  //void markShadowVbl(uint pcIdx, uint vblIdx) {
  //  shadow_vbls |= Cx::Tuple<uint,2>( pcIdx, vblIdx );
  //}
  void commit_initialization();

  void add_shadow_act(const ActSymm& act);

  bool integrityCk() const;

  bool shadowVblCk() const {
    return this->shadow_vbls_exist;
  }
  Cx::PFmla smoothShadowVbls(const Cx::PFmla& pf) const {
    return pf.smooth(shadow_pfmla_list_id);
  }
  Cx::PFmla smoothPuppetVbls(const Cx::PFmla& pf) const {
    return pf.smooth(puppet_pfmla_list_id);
  }

  void niceIdxFo(uint pcIdx, uint niceIdx) {
    niceIdcs[pcIdx] = niceIdx;
  }
  uint niceIdxOf(uint pcIdx) const {
    const uint* niceIdx = niceIdcs.lookup(pcIdx);
    if (!niceIdx) {
      return topology.pcs.sz() + pcIdx;
    }
    return *niceIdx;
  }
};
}

#if 0
class ActSet {
public:
  Set<uint> ids; ///< Action ids which make up this set.
  PF pfmla; ///< Formula representing the transitions.

  /// Indices of other action sets which this one conflicts with.
  Set<uint> conflicts;
  PF conflict_pfmla; ///< Formula representing the conflicting actions.
};
#endif

ostream&
OPut(ostream& of, const Xn::ActSymm& act);
PF
ClosedSubset(const PF& xnRel, const PF& invariant);
PF
LegitInvariant(const Xn::Sys& sys, const PF& loXnRel, const PF& hiXnRel);
bool
WeakConvergenceCk(const Xn::Sys& sys, const PF& xnRel, const PF& invariant);
bool
WeakConvergenceCk(const Xn::Sys& sys, const PF& xnRel);
bool
CycleCk(PF* scc, const PF& xnRel, const PF& pf);
bool
CycleCk(const PF& xnRel, const PF& pf);
PF
BackwardReachability(const PF& xnRel, const PF& pf);

#endif

