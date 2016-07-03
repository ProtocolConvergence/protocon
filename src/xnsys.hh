
#ifndef XnSys_HH_
#define XnSys_HH_

#include "cx/set.hh"
#include "cx/synhax.hh"
#include "cx/table.hh"
#include "cx/lgtable.hh"
#include "cx/alphatab.hh"
#include "cx/ofile.hh"
#include "cx/map.hh"
#include "pfmla.hh"
#include "xfmlae.hh"
#include "xnspec.hh"

extern Cx::OFile DBogOF;

#include "namespace.hh"

namespace Xn {
class Vbl;
class VblSymm;
class Pc;
class PcSymm;
class ActSymm;
class Net;

class NatPredicateMap {
public:
  Table< P::Fmla > membs;
  String expression;

  NatPredicateMap(uint nmembs) {
    for (uint i = 0; i < nmembs; ++i) {
      membs.push(P::Fmla(false));
    }
  }

  P::Fmla eval(uint i) const {
    Claim2( i ,<, membs.sz() );
    return membs[i];
  }

  bool constant_ck() const {
    for (uint i = 1; i < membs.sz(); ++i) {
      if (!membs[0].equiv_ck(membs[i]))
        return false;
    }
    return true;
  }
};

class LetPredicateMap {
public:
  Table<String> keys;
  Table<NatPredicateMap> vals;
  Map<String,uint> map;

  void add(const String& key, const NatPredicateMap& val) {
    keys.push(key);
    vals.push(val);
    map[key] = keys.sz()-1;
  }

  NatPredicateMap* lookup(const String& key) {
    uint* idx = map.lookup(key);
    if (!idx)  return 0;
    return &vals[*idx];
  }

  bool key_ck(const String& key) {
    return !!map.lookup(key);
  }
};

class PredicateMap {
public:
  Table<String> keys;
  Table<P::Fmla> pfmlas;
  Table<String> expressions;
  Map<String,uint> map;

  void add(const String& key, const P::Fmla& pf, const String& expression) {
    keys.push(key);
    pfmlas.push(pf);
    expressions.push(expression);
    map[key] = keys.sz()-1;
  }

  P::Fmla* lookup(const String& key) {
    uint* idx = map.lookup(key);
    if (!idx)  return 0;
    return &pfmlas[*idx];
  }

  bool key_ck(const String& key) {
    return !!map.lookup(key);
  }

  uint sz() const { return keys.sz(); }
};

class Vbl {
public:
  enum ShadowPuppetRole { Direct, Shadow, Puppet };
public:
  const VblSymm* symm;
  uint symm_idx;
  uint pfmla_idx; ///< Index of the variable (in a PmlaFCtx).
  bool random_flag;

  Vbl(VblSymm* symmetry, uint index)
    : symm(symmetry)
    , symm_idx(index)
    , pfmla_idx(UINT_MAX)
    , random_flag(false)
  {}

  bool random_ck() const { return random_flag; }
};

class VblSymm {
public:
  Mem<VblSymmSpec> spec;
  uint domsz;
  Table< Vbl* > membs;
  uint pfmla_list_id;
  Vbl::ShadowPuppetRole shadow_puppet_role;

  VblSymm()
    : shadow_puppet_role( Vbl::Direct )
  {}

  bool direct_ck() const { return shadow_puppet_role == Vbl::Direct; }
  bool pure_shadow_ck() const { return shadow_puppet_role == Vbl::Shadow; }
  bool pure_puppet_ck() const { return shadow_puppet_role == Vbl::Puppet; }

  bool shadow_ck() const { return pure_shadow_ck() || direct_ck(); }
  bool puppet_ck() const { return pure_puppet_ck() || direct_ck(); }
};

inline String name_of(const Vbl& vbl) {
  return vbl.symm->spec->name + "[" + vbl.symm_idx + "]";
}

class Pc {
public:
  const PcSymm* symm;
  uint symm_idx;
  /// The rvbls should include wvbls.
  Table< const Vbl* > rvbls;
  Table< const Vbl* > wvbls;
  P::Fmla act_unchanged_pfmla;
  P::Fmla closed_assume;
  P::Fmla invariant;
  P::Fmla puppet_xn;
  P::Fmla shadow_xn;
  X::Fmla permit_xn;
  X::Fmla forbid_xn;

  Pc(PcSymm* symmetry, uint index)
    : symm(symmetry)
    , symm_idx(index)
    , closed_assume(true)
    , invariant(true)
    , puppet_xn(false)
    , shadow_xn(false)
    , permit_xn(false)
    , forbid_xn(false)
  {}
  void actions(Table<uint>& ret_actions, PFmlaCtx& ctx) const;
};

class ActSymm {
public:
  const PcSymm* pc_symm;
  Table< uint > vals;
  uint pre_idx;
  uint img_idx;
  uint pre_idx_of_img;

  uint guard(uint vbl_idx) const;
  uint assign(uint vbl_idx) const;
  uint aguard(uint vbl_idx) const;
  void swap_vals(uint ridx_a, uint ridx_b);
  bool puppet_self_loop_ck() const;

  bool operator<(const Xn::ActSymm& b) const {
    return (this->vals < b.vals);
  }
  bool operator==(const Xn::ActSymm& b) const {
    return (this->vals == b.vals);
  }
  bool operator!=(const Xn::ActSymm& b) const {
    return !(*this == b);
  }
};

class PcSymm {
public:
  Mem<PcSymmSpec> spec;
  Table< Pc* > membs;
  int memb_idx_offset;
  /// The rvbls should include wvbls.
  Table< const VblSymm* > rvbl_symms;
  Table< const VblSymm* > wvbl_symms;
  Table< uint > wmap;
  std::vector< bool > write_flags;
  Table< NatMap > rindices;
  Table< NatMap > windices;
  /// Domains of readable variables.
  Table< uint > doms;
  Table< FlatSet< Xn::ActSymm > > conflicts;

  X::Fmla shadow_pfmla;
  X::Fmla direct_pfmla;
  LetPredicateMap predicate_map;

  uint act_idx_offset;
  uint n_possible_acts;

  uint pre_dom_offset;
  uint pre_domsz;
  uint img_domsz;
private:
  uint representative_pcidx;

public:
  PcSymm()
    : memb_idx_offset( 0 )
    , shadow_pfmla( false )
    , direct_pfmla( false )
  {
    InitDomMax( representative_pcidx );
  }

  String vbl_name(uint i) const {
    const String& name = rvbl_symms[i]->spec->name;
    return name + "[" + rindices[i].expression + "]";
  }

  bool write_ck(uint ridx) const {
    return write_flags[ridx];
  }

  bool dom_equiv_ck(const PcSymm& b) const;
  bool init_representative();
  bool representative(uint* ret_pcidx) const;
  void action(ActSymm& act, uint actidx) const;
  void actions(Table<uint>& ret_actions, PFmlaCtx& ctx) const;

  bool pure_shadow_ck() const {
    for (uint i = 0; i < rvbl_symms.sz(); ++i) {
      if (rvbl_symms[i]->pure_shadow_ck()) {
        return true;
      }
    }
    return false;
  }
};

inline String name_of(const Pc& pc) {
  return pc.symm->spec->name + "[" + pc.symm_idx + pc.symm->memb_idx_offset + "]";
}

inline uint ActSymm::guard(uint vbl_idx) const
{ return this->vals[vbl_idx]; }
inline uint ActSymm::assign(uint vbl_idx) const
{ return this->vals[this->pc_symm->rvbl_symms.sz() + vbl_idx]; }
inline uint ActSymm::aguard(uint vbl_idx) const
{ return this->guard(this->pc_symm->wmap[vbl_idx]); }
inline void ActSymm::swap_vals(uint ridx_a, uint ridx_b)
{
  SwapT( uint, this->vals[ridx_a], this->vals[ridx_b] );
  if (this->pc_symm->write_flags[ridx_a] ||
      this->pc_symm->write_flags[ridx_b])
  {
    Claim( this->pc_symm->write_flags[ridx_a] );
    Claim( this->pc_symm->write_flags[ridx_b] );
    uint widx_a = 0;
    uint widx_b = 0;
    for (uint i = 0; i < this->pc_symm->wmap.sz(); ++i) {
      if (this->pc_symm->wmap[i] == ridx_a) {
        widx_a = this->pc_symm->rvbl_symms.sz() + i;
      }
      if (this->pc_symm->wmap[i] == ridx_b) {
        widx_b = this->pc_symm->rvbl_symms.sz() + i;
      }
    }
    Claim2( widx_a ,!=, 0 );
    Claim2( widx_b ,!=, 0 );
    SwapT( uint, this->vals[widx_a], this->vals[widx_b] );
  }
}
inline bool ActSymm::puppet_self_loop_ck() const
{
  for (uint i = 0; i < this->pc_symm->wvbl_symms.sz(); ++i) {
    if (this->pc_symm->wvbl_symms[i]->pure_shadow_ck())
      continue;
    if (this->aguard(i) != this->assign(i))
      return false;
    if (this->pc_symm->spec->random_write_flags[this->pc_symm->wmap[i]]) {
      return false;
    }
  }
  return true;
}

class Net {
public:
  Mem<Spec> spec;
  PFmlaCtx pfmla_ctx;
  X::FmlaeCtx xfmlae_ctx;
  LgTable< Vbl > vbls;
  LgTable< VblSymm > vbl_symms;
  LgTable< Pc > pcs;
  LgTable< PcSymm > pc_symms;

private:
  Table< X::Fmlae > act_xfmlaes;
public:
  Table< Table<uint> > represented_actions;
  uint n_possible_acts;
  uint total_pre_domsz;
  bool lightweight;
  bool featherweight;
  X::Fmla identity_xn;

  bool random_write_exists;
  bool pure_shadow_vbl_exists;
  bool pure_puppet_vbl_exists;

private:
  uint shadow_pfmla_list_id;
  uint puppet_pfmla_list_id;
  uint pure_shadow_pfmla_list_id;
  uint pure_puppet_pfmla_list_id;

public:
  Net()
    : spec(0)
    , pfmla_ctx()
    , xfmlae_ctx(pfmla_ctx)
    , n_possible_acts(0)
    , total_pre_domsz(0)
    , lightweight(false)
    , featherweight(false)
    , identity_xn(true)
    , random_write_exists(false)
    , pure_shadow_vbl_exists(false)
    , pure_puppet_vbl_exists(false)
  {
    this->shadow_pfmla_list_id = this->pfmla_ctx.add_vbl_list();
    this->puppet_pfmla_list_id = this->pfmla_ctx.add_vbl_list();
    this->pure_shadow_pfmla_list_id = this->pfmla_ctx.add_vbl_list();
    this->pure_puppet_pfmla_list_id = this->pfmla_ctx.add_vbl_list();
  }

  void commit_initialization();
  void fixup_pc_xns();

  VblSymm*
  add_variables(const String& name, uint nmembs, uint domsz,
                Vbl::ShadowPuppetRole role = Vbl::Direct);
private:
  void commit_variable(VblSymm& symm, uint i);
public:
  void commit_variables();
  PcSymm*
  add_processes(const String& name, const String& idx_name, uint nmembs);
  void
  add_read_access (PcSymm* pc_symm, const VblSymm* vbl_symm,
                   const NatMap& indices);
  void
  add_write_access (PcSymm* pc_symm, const VblSymm* vbl_symm,
                    const NatMap& indices);

  uint action_pcsymm_index(uint actidx) const;
  void action(ActSymm& act, uint actidx) const;
  uint action_index(const ActSymm& act) const;

  uint action_pre_index(uint actidx) const;
  uint action_img_index(uint actidx) const;

  uint representative_action_index(uint actidx) const;

  const X::Fmla action_pfmla(uint actidx) const {
    if (!this->lightweight) {
      return act_xfmlaes[actidx].xfmla();
    }
    X::Fmla xn(false);
    const Table<uint>& actions = represented_actions[actidx];
    for (uint i = 0; i < actions.sz(); ++i) {
      X::Fmla tmp_xn;
      this->make_action_pfmla(&tmp_xn, actions[i]);
      xn |= tmp_xn;
    }
    return xn;
  }

  const X::Fmlae action_xfmlae(uint actidx) const {
    if (!this->lightweight) {
      return act_xfmlaes[actidx];
    }
    X::Fmlae xn(&this->xfmlae_ctx);
    const Table<uint>& actions = represented_actions[actidx];
    for (uint i = 0; i < actions.sz(); ++i) {
      X::Fmlae tmp_xn;
      this->make_action_xfmlae(&tmp_xn, actions[i]);
      xn |= tmp_xn;
    }
    return xn;
  }

  PFmlaVbl pfmla_vbl(uint i) const {
    return this->pfmla_ctx.vbl(this->vbls[i].pfmla_idx);
  }
  PFmlaVbl pfmla_vbl(const Vbl& x) const {
    return this->pfmla_ctx.vbl(x.pfmla_idx);
  }

  bool probabilistic_ck() const {
    return random_write_exists;
  }
  bool pure_shadow_vbl_ck() const {
    return pure_shadow_vbl_exists;
  }

  bool safe_ck(const Xn::ActSymm& act) const;

  Cx::PFmla smooth_pure_shadow_vbls(const Cx::PFmla& pf) const {
    if (!pure_shadow_vbl_exists) {
      return pf;
    }
    return pf.smooth(pure_shadow_pfmla_list_id);
  }
  Cx::PFmla smooth_shadow_vbls(const Cx::PFmla& pf) const {
    return pf.smooth(shadow_pfmla_list_id);
  }

  Cx::PFmla smooth_puppet_vbls(const Cx::PFmla& pf) const {
    return pf.smooth(puppet_pfmla_list_id);
  }

  Cx::PFmla smooth_pure_puppet_vbls(const Cx::PFmla& pf) const {
    if (!pure_puppet_vbl_exists) {
      return pf;
    }
    return pf.smooth(pure_puppet_pfmla_list_id);
  }
  Cx::PFmla smooth_pure_puppet_img_vbls(const Cx::PFmla& pf) const {
    if (!pure_puppet_vbl_exists) {
      return pf;
    }
    return pf.smooth_img(pure_puppet_pfmla_list_id);
  }

  Cx::PFmla proj_shadow(const Cx::PFmla& pf) const {
    return this->smooth_pure_puppet_vbls(pf);
  }
  Cx::PFmla proj_img_shadow(const Cx::PFmla& pf) const {
    return this->smooth_pure_puppet_img_vbls(pf);
  }
  Cx::PFmla proj_puppet(const Cx::PFmla& pf) const {
    return this->smooth_pure_shadow_vbls(pf);
  }

  ostream& oput(ostream& of,
                const Cx::PFmla& pf,
                const String& pfx,
                const String& sfx) const;

  OFile& oput_vbl_names(OFile& ofile) const;
  OFile& oput_pfmla(OFile& ofile, Cx::PFmla pf,
                    Sign pre_or_img, bool just_one) const;
  OFile& oput_one_xn(OFile& ofile, const X::Fmla& pf) const;
  OFile& oput_all_xn(OFile& ofile, const X::Fmla& pf) const;
  OFile& oput_one_pf(OFile& ofile, const P::Fmla& pf) const;
  OFile& oput_all_pf(OFile& ofile, const P::Fmla& pf) const;


  X::Fmla sync_xn(const Table<uint>& actidcs) const;
  X::Fmla xn_of_pc(const Xn::ActSymm& act, uint pcidx) const;
  X::Fmla represented_xns_of_pc(const Xn::ActSymm& act, uint relative_pcidx) const;
  void make_action_pfmla(X::Fmla* ret_xn, uint actid) const;
  void make_action_xfmlae(X::Fmlae* ret_xn, uint actidx) const;
private:
  void cache_action_xfmla(uint actid);
};

/** This holds the search problem and its solution.**/
class Sys {
public:
  Xn::Net topology;
  Xn::Spec spec[1];
  vector<uint> actions; ///< Force use of these actions.

  PredicateMap predicate_map;

  /// Assumed state predicate which must remain closed.
  P::Fmla closed_assume;
  /// Invariant to which we should converge.
  P::Fmla invariant;
  bool shadow_puppet_synthesis;
  X::Fmla shadow_pfmla;
  /// Transition relation within the invariant.
  X::Fmla direct_pfmla;
  /// Self-loops in the invariant.
  X::Fmla shadow_self;

private:
  Map<uint,uint> niceIdcs; ///< Niceness for process symmetries, used in search.

public:
  Sys()
    : closed_assume( true )
    , invariant( true )
    , shadow_puppet_synthesis(false)
    , shadow_pfmla(false)
    , direct_pfmla(false)
  {
    topology.spec = spec;
  }

  void commit_initialization();

  bool integrityCk() const;

  /// Do the shadow puppet synthesis
  bool shadow_puppet_synthesis_ck() const {
    return this->shadow_puppet_synthesis;
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

class ManySys : public LgTable<Sys>
{
public:
  ManySys() {}
};
}

OFile&
OPut(OFile& of, const Xn::ActSymm& act);
void
find_one_cycle(Table<P::Fmla>& states,
               const X::Fmla& xn, const P::Fmla& scc,
               const P::Fmla& initial);
void
find_one_cycle(Table<P::Fmla>& states,
               const X::Fmla& xn, const P::Fmla& scc);
void
find_livelock_actions(Table<uint>& actions, const X::Fmla& xn,
                      const P::Fmla& scc, const P::Fmla& invariant,
                      const Xn::Net& topo);
void
oput_one_cycle(OFile& of, const X::Fmla& xn,
               const P::Fmla& scc, const P::Fmla& initial,
               const Xn::Net& topo);
bool
candidate_actions(std::vector<uint>& candidates,
                  Table<uint>& dels,
                  Table<uint>& rejs,
                  const Xn::Sys& sys);

END_NAMESPACE
#endif

