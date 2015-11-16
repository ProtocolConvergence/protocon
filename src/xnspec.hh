
#ifndef XnSpec_HH_
#define XnSpec_HH_

#include "cx/set.hh"
#include "cx/synhax.hh"
#include "cx/table.hh"
#include "cx/lgtable.hh"
#include "cx/alphatab.hh"
#include "cx/map.hh"

extern Cx::OFile DBogOF;

namespace Xn {
using Cx::String;

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
  FutureActiveShadow,
  //FutureActive,
  NInvariantBehavs
};

class NatMap {
public:
  Cx::Table< int > membs;
  String expression;

  NatMap() {}

  explicit NatMap(uint nmembs) {
    for (uint i = 0; i < nmembs; ++i) {
      membs.push(i);
    }
  }

  const NatMap& operator=(int x) {
    membs.resize(1);
    membs[0] = x;
    expression = x;
    return *this;
  }

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

class VblSymmSpec {
public:
  String name;
  String domsz_expression;
  String nmembs_expression;
};

class LinkSymmetry {
private:
  Cx::Table<uint> t;
public:
  uint nlinks;
  uint nvbls;

  Cx::String let_expression;
  Cx::String multiset_expression;
  Cx::Table<Cx::String> index_expressions;

public:
  explicit LinkSymmetry(uint _nlinks)
  : nlinks(_nlinks)
  , nvbls(0)
  {
  }

  void add_link_symmetry(const Cx::Table<uint>& ob, const Cx::String& index_expression) {
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
      Cx::Table<uint> min_row(ncols);
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
  Cx::String name;
  Cx::String idx_name;
  Cx::String closed_assume_expression;
  Cx::String invariant_expression;
  LetVblMap let_map;
  Cx::Table<const VblSymmSpec*> rvbl_symms;
  Cx::Table<const VblSymmSpec*> wvbl_symms;
  Cx::Table<bool> random_read_flags;
  Cx::Table<bool> random_write_flags;
  Cx::Table<LinkSymmetry> link_symmetries;
  Cx::String nmembs_expression;
  Cx::Table<Cx::String> shadow_act_strings;
  Cx::Table<Cx::String> forbid_act_strings;
  Cx::Table<Cx::String> permit_act_strings;
};

class Spec {
public:
  Cx::LgTable<PcSymmSpec> pc_symms;
  Cx::LgTable<VblSymmSpec> vbl_symms;

  LetVblMap constant_map;
  InvariantStyle invariant_style;
  InvariantScope invariant_scope;
  InvariantBehav invariant_behav;
  Cx::String closed_assume_expression;
  Cx::String invariant_expression;

  Spec()
    : invariant_style( Xn::FutureAndShadow )
    , invariant_scope( Xn::DirectInvariant )
    , invariant_behav( Xn::NInvariantBehavs )
  {}
};
}

#endif

