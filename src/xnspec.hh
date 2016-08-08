
#ifndef XnSpec_HH_
#define XnSpec_HH_

#include "cx/set.hh"
#include "cx/synhax.hh"
#include "cx/table.hh"
#include "cx/lgtable.hh"
#include "cx/alphatab.hh"
#include "cx/map.hh"

extern Cx::OFile DBogOF;

#include "namespace.hh"

namespace Xn {
class NatMap;
class LetVblMap;
class LinkSymmetry;
class VblSymmSpec;
class VblSymmAccessSpec;
class PcSymmSpec;
class Spec;

enum VariableAccessType {
  ReadAccess,
  WriteAccess,
  YieldAccess,
  EffectAccess,
  RandomReadAccess,
  RandomWriteAccess,
  NVariableAccessTypes
};

enum ShadowPuppetRole {
  Direct,
  Shadow,
  Puppet,
  NShadowPuppetRoles
};

enum InvariantStyle {
  FutureAndClosed,
  FutureAndSilent,
  FutureAndShadow,
  FutureAndActiveShadow,
  NInvariantStyles
};

enum InvariantScope {
  DirectInvariant,
  ShadowInvariant,
  FutureInvariant,
  NInvariantScopes
};

enum InvariantBehav {
  // SilentBehav
  // ActiveBehav
  FutureSilent,
  FutureShadow,
  FutureActiveShadow,
  //FutureActive,
  NInvariantBehavs
};

class NatMap {
public:
  Table< int > membs;
  String expression;
  bool scalar;

  NatMap() : scalar(true) {}

  explicit NatMap(uint nmembs) : scalar(true) {
    for (uint i = 0; i < nmembs; ++i) {
      membs.push(i);
    }
  }

  const NatMap& operator=(int x) {
    scalar = true;
    membs.resize(1);
    membs[0] = x;
    expression = x;
    return *this;
  }

  uint sz() const { return membs.sz(); }

  int eval(uint i) const {
    Claim2( i ,<, membs.sz() );
    return membs[i];
  }

  uint index(uint i, uint m) const {
    return umod_int (eval (i), m);
  }

  bool constant_ck() const {
    for (uint i = 1; i < membs.sz(); ++i) {
      if (membs[i] != membs[0])
        return false;
    }
    return true;
  }
};

class LetVblMap {
public:
  Table<String> keys;
  Table<NatMap> vals;
  Map<String,uint> map;

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


class LinkSymmetry {
private:
  Table<uint> t;
public:
  uint nlinks;
  uint nvbls;

  String let_expression;
  String multiset_expression;
  Table<String> index_expressions;

public:
  explicit LinkSymmetry(uint _nlinks)
  : nlinks(_nlinks)
  , nvbls(0)
  {
  }

  void add_link_symmetry(const Table<uint>& ob, const String& index_expression) {
    Claim2( ob.sz() ,==, nlinks );
    ++nvbls;
    index_expressions.push(index_expression);
    for (uint i = 0; i < nlinks; ++i) {
      t.push(ob[i]);
    }
  }

  uint& operator()(uint i, uint j)
  { return t[i*nlinks+j]; }

  const uint& operator()(uint i, uint j) const
  { return t[i*nlinks+j]; }

  bool elem_ck(uint e) const
  { return t.elem_ck(e); }

#if 0
  bool permute_minimal(uint* a) const
  {
    bool looping = true;
    bool changed = false;
    if (nrows == 0)
      return false;
    for (uint row_off = 0; row_off < nrows-1; ++row_off)
    {
      Table<uint> min_row(ncols);
      uint min_row_idx = row_off;
      for (uint j = 0; j < ncols; ++j) {
        min_row[j] = a[(*this)(row_off,j)];
      }
      for (uint i = row_off+1; i < nrows; ++i) {
        for (uint j = 0; j < ncols; ++j) {
          if (min_row[j] < a[(*this)(i,j)]) {
          }
          min_row[j] = a[(*this)(row_off,j)];
        }
      }

    while (looping)
    {
      looping = false;
      for (uint i = 0; i < t.sz(); i+=n) {
        for (uint j = 0; j < n; ++j) {
        }
      }
    }
  }
#endif
};


class VblSymmSpec {
public:
  String name;
  String domsz_expression;
  String nmembs_expression;
  uint domsz;
  ShadowPuppetRole shadow_puppet_role;

  VblSymmSpec()
    : domsz(0)
    , shadow_puppet_role(Xn::Direct)
  {}

  bool direct_ck() const { return shadow_puppet_role == Xn::Direct; }
  bool pure_shadow_ck() const { return shadow_puppet_role == Xn::Shadow; }
  bool pure_puppet_ck() const { return shadow_puppet_role == Xn::Puppet; }

  bool shadow_ck() const { return pure_shadow_ck() || direct_ck(); }
  bool puppet_ck() const { return pure_puppet_ck() || direct_ck(); }
};

class VblSymmAccessSpec {
public:
  Mem<const VblSymmSpec> vbl_symm;
  VariableAccessType type;
  String index_expression;

  VblSymmAccessSpec()
    : type(Xn::NVariableAccessTypes)
  {}

  bool write_ck() const {
    return
     (   type == Xn::WriteAccess
      || type == Xn::YieldAccess
      || type == Xn::EffectAccess
      || type == Xn::RandomWriteAccess
     );
  }
  bool read_ck() const {
    return
     (   type == Xn::ReadAccess
      || type == Xn::WriteAccess
      || type == Xn::RandomReadAccess
      || type == Xn::RandomWriteAccess
     );
  }

  bool synt_read_ck() const {
    return read_ck() && vbl_symm->puppet_ck();
  }
  bool synt_write_ck() const {
    return write_ck();
  }

  bool synt_readonly_ck() const {
    return synt_read_ck() && !synt_write_ck();
  }
  bool synt_writeonly_ck() const {
    return !synt_read_ck() && synt_write_ck();
  }

  bool random_read_ck() const { return (type == Xn::RandomReadAccess); }
  bool random_write_ck() const { return (type == Xn::RandomWriteAccess); }
  bool random_ck() const { return (random_read_ck() || random_write_ck()); }

  bool direct_ck()      const { return vbl_symm->direct_ck(); }
  bool pure_shadow_ck() const { return vbl_symm->pure_shadow_ck(); }
  bool pure_puppet_ck() const { return vbl_symm->pure_puppet_ck(); }
  bool shadow_ck()      const { return vbl_symm->shadow_ck(); }
  bool puppet_ck()      const { return vbl_symm->puppet_ck(); }

  uint domsz() const {
    return vbl_symm->domsz;
  }
  uint rdomsz() const {
    if (!synt_read_ck())  return 1;
    return domsz();
  }
  uint wdomsz() const {
    if (!write_ck())  return 0;
    if (random_write_ck())  return 1;
    if (vbl_symm->pure_shadow_ck())  return domsz()+1;
    if (type == Xn::EffectAccess)  return domsz()+1;
    return domsz();
  }
};

class PcSymmSpec {
public:
  String name;
  String idx_name;
  String closed_assume_expression;
  String invariant_expression;
  LetVblMap let_map;

  Table<VblSymmAccessSpec> access;
  Table<uint> wmap;
  Table<LinkSymmetry> link_symmetries;
  String nmembs_expression;
  String idxmap_name;
  String idxmap_expression;
  Table<String> shadow_act_strings;
  Table<String> forbid_act_strings;
  Table<String> permit_act_strings;


  const VblSymmAccessSpec& waccess(uint i) const {
    return access[wmap[i]];
  }


#define ExistsAccess(f) \
  for (uint i = 0; i < access.sz(); ++i) { \
    if (access[i].f##_ck())  return true; \
  } \
  return false

  bool random_read_ck() const { ExistsAccess(random_read); }
  bool random_write_ck() const { ExistsAccess(random_write); }
  bool random_ck() const { ExistsAccess(random); }
  bool synt_writeonly_ck() const { ExistsAccess(synt_writeonly); }

#undef ExistsAccess
};

class Spec {
public:
  LgTable<PcSymmSpec> pc_symms;
  LgTable<VblSymmSpec> vbl_symms;

  LetVblMap constant_map;
  InvariantStyle invariant_style;
  InvariantScope invariant_scope;
  InvariantBehav invariant_behav;
  String closed_assume_expression;
  String invariant_expression;

  Spec()
    : invariant_style( Xn::FutureAndShadow )
    , invariant_scope( Xn::DirectInvariant )
    , invariant_behav( Xn::NInvariantBehavs )
  {}

  bool active_shadow_ck() const {
    return (invariant_style == Xn::FutureAndActiveShadow
            ||
            invariant_behav == Xn::FutureActiveShadow);
  }
};
}

END_NAMESPACE
#endif

