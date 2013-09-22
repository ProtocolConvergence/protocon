
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
#include "tuple.hh"

extern Cx::OFile DBogOF;

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
  String expression;

  NatMap(uint nmembs) {
    for (uint i = 0; i < nmembs; ++i) {
      membs.push(i);
    }
  }

  int eval(uint i) const {
    Claim2( i ,<, membs.sz() );
    return membs[i];
  }

  uint index(uint i, uint m) const {
    return umod_int (eval (i), m);
  }
};

class LetVblMap {
public:
  Cx::Table<String> keys;
  Cx::Table<NatMap> vals;
  Cx::Map<String,uint> map;

  void add(const String& key, const NatMap& val) {
    keys.push(key);
    vals.push(val);
    map[key] = keys.sz()-1;
  }

  NatMap* lookup(const String& key) {
    uint* idx = map.lookup(key);
    if (!idx)  return 0;
    return &vals[*idx];
  }

  bool key_ck(const String& key) {
    return !!map.lookup(key);
  }
};

class Vbl {
public:
  enum ShadowPuppetRole { Direct, Shadow, Puppet };
public:
  const VblSymm* symm;
  uint symm_idx;
  uint pfmla_idx; ///< Index of the variable (in a PmlaFCtx).

  Vbl(VblSymm* symmetry, uint index)
    : symm(symmetry)
    , symm_idx(index)
    , pfmla_idx(Max_uint)
  {}
};

class VblSymm {
public:
  uint domsz;
  String name;
  String domsz_expression;
  String nmembs_expression;
  Cx::Table< Vbl* > membs;
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
  uint pre_idx;
  uint img_idx;
  uint pre_idx_of_img;

  uint guard(uint vbl_idx) const;
  uint assign(uint vbl_idx) const;
  uint aguard(uint vbl_idx) const;
};

class PcSymm {
public:
  String name;
  String nmembs_expression;
  Cx::Table< Pc* > membs;
  LetVblMap let_map;
  /// The rvbls should include wvbls.
  Cx::Table< const VblSymm* > rvbl_symms;
  Cx::Table< const VblSymm* > wvbl_symms;
  Cx::Table< uint > wmap;
  std::vector< bool > write_flags;
  Cx::Table< NatMap > rindices;
  Cx::Table< NatMap > windices;
  /// Domains of readable variables.
  Cx::Table< uint > doms;
  String idx_name;

  Cx::PFmla shadow_pfmla;
  Cx::PFmla direct_pfmla;

  Cx::Table<Cx::String> shadow_act_strings;

  uint act_idx_offset;
  uint n_possible_acts;

  uint pre_dom_offset;
  uint pre_domsz;
  uint img_domsz;

  PcSymm()
    : shadow_pfmla( false )
    , direct_pfmla( false )
  {}

  String vbl_name(uint i) const {
    const String& name = rvbl_symms[i]->name;
    return name + "[" + rindices[i].expression + "]";
  }

  bool write_ck(uint ridx) const {
    return write_flags[ridx];
  }

  void action(ActSymm& act, uint actidx) const;
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

  LetVblMap constant_map;
  Cx::Table< Cx::PFmla > act_pfmlas;
  uint n_possible_acts;
  uint total_pre_domsz;
  Cx::PFmla identity_pfmla;

  bool puppet_vbl_exists;
  bool pure_puppet_vbl_exists;

private:
  uint shadow_pfmla_list_id;
  uint puppet_pfmla_list_id;
  uint pure_puppet_pfmla_list_id;

public:
  Net()
    : n_possible_acts(0)
    , total_pre_domsz(0)
    , identity_pfmla(true)
    , puppet_vbl_exists(false)
    , pure_puppet_vbl_exists(false)
  {
    this->shadow_pfmla_list_id = this->pfmla_ctx.add_vbl_list();
    this->puppet_pfmla_list_id = this->pfmla_ctx.add_vbl_list();
    this->pure_puppet_pfmla_list_id = this->pfmla_ctx.add_vbl_list();
  }

  void commit_initialization();

  VblSymm*
  add_variables(const String& name, uint nmembs, uint domsz,
                Vbl::ShadowPuppetRole role = Vbl::Direct);
  PcSymm*
  add_processes(const String& name, uint nmembs);
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

  const Cx::PFmla& action_pfmla(uint i) const {
    return act_pfmlas[i];
  }

  Cx::PFmlaVbl pfmla_vbl(uint i) {
    return this->pfmla_ctx.vbl(this->vbls[i].pfmla_idx);
  }
  Cx::PFmlaVbl pfmla_vbl(const Vbl& x) {
    return this->pfmla_ctx.vbl(x.pfmla_idx);
  }

  Cx::PFmla smooth_shadow_vbls(const Cx::PFmla& pf) const {
    return pf.smooth(shadow_pfmla_list_id);
  }
  Cx::PFmla smooth_puppet_vbls(const Cx::PFmla& pf) const {
    if (!puppet_vbl_exists) {
      return pf;
    }
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

  ostream& oput(ostream& of,
                const Cx::PFmla& pf,
                const String& pfx,
                const String& sfx) const;

  Cx::OFile& oput_pfmla(Cx::OFile& of, Cx::PFmla pf,
                        Sign pre_or_img, bool just_one) const;
  Cx::OFile& oput_one_xn(Cx::OFile& of, const Cx::PFmla& pf) const;
  Cx::OFile& oput_all_xn(Cx::OFile& of, const Cx::PFmla& pf) const;
  Cx::OFile& oput_all_pf(Cx::OFile& of, const Cx::PFmla& pf) const;

private:
  void make_action_pfmla(uint actid);
};

/** This holds the search problem and its solution.**/
class Sys {
public:
  Xn::Net topology;
  vector<uint> actions; ///< Force use of these actions.

  /// Invariant to which we should converge.
  Cx::PFmla invariant;
  Cx::String invariant_expression;
  /// Transition relation within the invariant.
  bool shadow_puppet_synthesis;
  bool direct_invariant_flag;
  Cx::PFmla shadow_pfmla;
  Cx::PFmla direct_pfmla;
  /// Self-loops in the invariant.
  Cx::PFmla shadow_self;

private:
  Map<uint,uint> niceIdcs; ///< Niceness for process symmetries, used in search.

public:
  Sys()
    : invariant( true )
    , shadow_puppet_synthesis(false)
    , direct_invariant_flag(true)
    , shadow_pfmla(false)
    , direct_pfmla(false)
  {
  }

  void commit_initialization();

  bool integrityCk() const;

  /// Do the shadow puppet synthesis
  bool shadow_puppet_synthesis_ck() const {
    return this->shadow_puppet_synthesis;
  }
  bool direct_invariant_ck() const {
    return this->direct_invariant_flag;
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

class ManySys : public Cx::LgTable<Sys>
{
public:
  ManySys() {}
};
}

Cx::OFile&
OPut(Cx::OFile& of, const Xn::ActSymm& act);
PF
LegitInvariant(const Xn::Sys& sys, const PF& loXnRel, const PF& hiXnRel,
               const Cx::PFmla* scc=0);
bool
WeakConvergenceCk(const Xn::Sys& sys, const PF& xnRel, const PF& invariant);
bool
WeakConvergenceCk(const Xn::Sys& sys, const PF& xnRel);

#endif

