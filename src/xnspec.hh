
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
class PcSymmSpec;
class LinkSymmetry;
class Spec;

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

class VblSymmSpec {
public:
  String name;
  String domsz_expression;
  String nmembs_expression;
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

class PcSymmSpec {
public:
  String name;
  String idx_name;
  String closed_assume_expression;
  String invariant_expression;
  LetVblMap let_map;
  Table<const VblSymmSpec*> rvbl_symms;
  Table<const VblSymmSpec*> wvbl_symms;
  Table<bool> random_read_flags;
  Table<bool> random_write_flags;
  Table<LinkSymmetry> link_symmetries;
  String nmembs_expression;
  String offset_expression;
  Table<String> shadow_act_strings;
  Table<String> forbid_act_strings;
  Table<String> permit_act_strings;
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

