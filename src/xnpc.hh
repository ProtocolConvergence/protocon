
#ifndef XnPc_HH_
#define XnPc_HH_

#include "cx/synhax.hh"

#include "cx/set.hh"
#include "cx/table.hh"
#include "cx/alphatab.hh"
#include "cx/map.hh"
#include "xfmlae.hh"
#include "xnspec.hh"

#include "namespace.hh"
namespace Xn {
class Vbl;
class VblSymm;
class ActSymm;
class Pc;
class PcSymm;

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

  VblSymm()
  {}

  bool direct_ck() const { return spec->direct_ck(); }
  bool pure_shadow_ck() const { return spec->pure_shadow_ck(); }
  bool pure_puppet_ck() const { return spec->pure_puppet_ck(); }

  bool shadow_ck() const { return spec->shadow_ck(); }
  bool puppet_ck() const { return spec->puppet_ck(); }
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
  bool readable_self_loop_ck() const;

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
  NatMap mapped_indices;
  /// The rvbls should include wvbls.
  Table< const VblSymm* > rvbl_symms;
  Table< const VblSymm* > wvbl_symms;
  Table< NatMap > vbl_indices;
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
    : shadow_pfmla( false )
    , direct_pfmla( false )
  {
    InitDomMax( representative_pcidx );
  }

  String vbl_name(uint i) const {
    const String& name = rvbl_symms[i]->spec->name;
    return name + "[" + vbl_indices[i].expression + "]";
  }

  bool read_ck(uint ridx) const {
    return spec->access[ridx].read_ck();
  }
  bool write_ck(uint ridx) const {
    return spec->access[ridx].write_ck();
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
  return pc.symm->spec->name + "[" + pc.symm->mapped_indices.eval(pc.symm_idx) + "]";
}

inline uint ActSymm::guard(uint vbl_idx) const
{ return this->vals[vbl_idx]; }
inline uint ActSymm::assign(uint vbl_idx) const
{ return this->vals[this->pc_symm->rvbl_symms.sz() + vbl_idx]; }
inline uint ActSymm::aguard(uint vbl_idx) const
{ return this->guard(this->pc_symm->spec->wmap[vbl_idx]); }
inline void ActSymm::swap_vals(uint ridx_a, uint ridx_b)
{
  SwapT( uint, this->vals[ridx_a], this->vals[ridx_b] );
  if (this->pc_symm->write_ck(ridx_a) ||
      this->pc_symm->write_ck(ridx_b))
  {
    Claim( this->pc_symm->write_ck(ridx_a) );
    Claim( this->pc_symm->write_ck(ridx_b) );
    uint widx_a = 0;
    uint widx_b = 0;
    for (uint i = 0; i < this->pc_symm->wvbl_symms.sz(); ++i) {
      if (this->pc_symm->spec->wmap[i] == ridx_a) {
        widx_a = this->pc_symm->rvbl_symms.sz() + i;
      }
      if (this->pc_symm->spec->wmap[i] == ridx_b) {
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
    const VblSymmAccessSpec& access = this->pc_symm->spec->waccess(i);
    if (access.synt_writeonly_ck()) {
      if (access.vbl_symm->puppet_ck()) {
        if (this->assign(i) != access.vbl_symm->domsz)
          return false;
      }
      continue;
    }
    if (this->aguard(i) != this->assign(i))
      return false;
    if (access.random_write_ck()) {
      return false;
    }
  }
  return true;
}

inline bool ActSymm::readable_self_loop_ck() const
{
  for (uint i = 0; i < this->pc_symm->wvbl_symms.sz(); ++i) {
    const VblSymmAccessSpec& access = this->pc_symm->spec->waccess(i);
    if (!access.synt_read_ck())
      continue;
    if (access.random_write_ck()) {
      return false;
    }
    if (this->aguard(i) != this->assign(i))
      return false;
  }
  return true;
}

}
END_NAMESPACE
#endif

