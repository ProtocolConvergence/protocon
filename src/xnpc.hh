
#ifndef XnPc_HH_
#define XnPc_HH_
#include <sstream>

#include "cx/set.hh"
#include "cx/table.hh"
#include "cx/alphatab.hh"
#include "cx/map.hh"
#include "xfmlae.hh"
#include "xnspec.hh"

#include "cx/synhax.hh"

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

inline std::string name_of(const Vbl& vbl) {
  std::ostringstream oss;
  oss << vbl.symm->spec->name << '[' << vbl.symm_idx << ']';
  return oss.str();
}

class ActSymm {
public:
  const PcSymm* pc_symm;
  // TODO: Use PcSymmSpec instead of PcSymm if possible.
  //const PcSymmSpec* pc_spec;
  Table< uint > vals;
  uint pre_idx;
  uint img_idx;
  uint pre_idx_of_img;

  bool operator< (const Xn::ActSymm& b) const { return (this->vals < b.vals); }
  bool operator==(const Xn::ActSymm& b) const { return (this->vals == b.vals); }
  bool operator!=(const Xn::ActSymm& b) const { return !(*this == b); }

  uint guard(uint vbl_idx) const;
  uint assign(uint vbl_idx) const;
  uint aguard(uint vbl_idx) const;
  uint& guard(uint vbl_idx);
  uint& assign(uint vbl_idx);
  uint& aguard(uint vbl_idx);

  bool puppet_self_loop_ck() const;
  bool readable_self_loop_ck() const;
  void swap_vals(uint ridx_a, uint ridx_b);
};

uint id_of(const ActSymm& act);


class Pc {
public:
  const PcSymm* symm;
  uint symm_idx;
  /// The rvbls should include wvbls.
  Table< const Vbl* > rvbls;
  Table< const Vbl* > wvbls;
  P::Fmla global_mask_xn;
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

  std::string vbl_name(uint i) const {
    std::ostringstream oss;
    oss << rvbl_symms[i]->spec->name
      << '[' << vbl_indices[i].expression << ']';
    return oss.str();
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
  ActSymm act_of(uint actidx) const;
  void action(ActSymm& act, uint actidx) const { act = act_of(actidx); }
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

inline std::string name_of(const Pc& pc) {
  std::ostringstream oss;
  oss << pc.symm->spec->name
    << '[' << pc.symm->mapped_indices.eval(pc.symm_idx) << ']';
  return oss.str();
}

inline uint ActSymm::guard (uint vidx) const { return vals[vidx]; }
inline uint ActSymm::assign(uint vidx) const { return vals[pc_symm->rvbl_symms.sz() + vidx]; }
inline uint ActSymm::aguard(uint vidx) const { return vals[pc_symm->spec->wmap[vidx]]; }

inline uint& ActSymm::guard (uint vidx) { return vals[vidx]; }
inline uint& ActSymm::assign(uint vidx) { return vals[pc_symm->rvbl_symms.sz() + vidx]; }
inline uint& ActSymm::aguard(uint vidx) { return vals[pc_symm->spec->wmap[vidx]]; }

}
END_NAMESPACE
#endif

