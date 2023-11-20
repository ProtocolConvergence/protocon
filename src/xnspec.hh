
#ifndef XnSpec_HH_
#define XnSpec_HH_
#include <memory>

#include "cx/set.hh"
#include "cx/synhax.hh"
#include "cx/table.hh"
#include "cx/lgtable.hh"
#include "cx/map.hh"

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
  NatMap() {}
  explicit NatMap(unsigned n) {
    scalar = false;
    a_.resize(n);
    for (unsigned i = 0; i < n; ++i) {
      a_[i] = i;
    }
  }

  NatMap(NatMap&& m) = default;
  explicit NatMap(const NatMap& m) {
    scalar = m.scalar;
    a_ = m.a_;
    this->assign_expression(m.expression());
  }

  NatMap copy() const {
    NatMap m;
    m.scalar = scalar;
    m.a_ = a_;
    if (expression_) {
      m.assign_expression(*expression_);
    }
    return m;
  }

  void clear() {
    scalar = true;
    a_.clear();
    expression_.reset(NULL);
  }
  const NatMap& operator=(int x) {
    scalar = true;
    a_.resize(1);
    a_[0] = x;
    this->assign_expression(std::to_string(x));
    return *this;
  }

  int* elt(unsigned i) {return &a_[i];}
  void assign_at(unsigned i, int x) {a_[i] = x;}
  int at(unsigned i) const {return a_[i];}
  unsigned size() const {return a_.size();}

  uint sz() const { return this->size();}

  int eval(uint i) const {
    Claim2( i ,<, this->size() );
    return a_[i];
  }

  uint index(uint i, uint m) const {
    return umod_int (eval (i), m);
  }

  bool constant_ck() const {
    for (unsigned i = 1; i < a_.size(); ++i) {
      if (a_[i] != a_[0]) {
        return false;
      }
    }
    return true;
  }

  void push_back(int x) {
    scalar = false;
    a_.push_back(x);
    expression_.reset(NULL);
  }

  std::string_view expression() const {
    if (!expression_) {return "";}
    return *expression_;
  }
  void assign_expression(std::string_view s) {
    if (!expression_) {
      expression_.reset(new std::string);
    }
    *expression_ = s;
  }

 public:
  bool scalar = true;
 private:
  std::vector<int> a_;
  std::unique_ptr<std::string> expression_;
};

class LetVblMap {
public:
  std::vector<std::string> keys;
  std::vector<NatMap> vals;
  Map<std::string,uint> map;

  void add(const std::string& key, const NatMap& val) {
    keys.push_back(key);
    vals.push_back(val.copy());
    map[key] = keys.size()-1;
  }

  NatMap* lookup(const std::string& key) {
    uint* idx = map.lookup(key);
    if (!idx)  return 0;
    return &vals[*idx];
  }

  bool key_ck(const std::string& key) {
    return !!map.lookup(key);
  }
};


class LinkSymmetry {
private:
  Table<uint> t;
public:
  uint nlinks;
  uint nvbls;

  std::string let_expression;
  std::string multiset_expression;
  Table<std::string> index_expressions;

public:
  explicit LinkSymmetry(uint _nlinks)
  : nlinks(_nlinks)
  , nvbls(0)
  {
  }

  void add_link_symmetry(const Table<uint>& ob, const std::string& index_expression) {
    Claim2( ob.sz() ,==, nlinks );
    ++nvbls;
    index_expressions.push_back(index_expression);
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
  std::string name;
  std::string domsz_expression;
  std::string nmembs_expression;
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

  std::string_view index_expression() const {
    if (!index_expression_) {return "";}
    return *index_expression_;
  }
  void assign_index_expression(std::string_view s) {
    if (!index_expression_) {
      index_expression_.reset(new std::string);
    }
    *index_expression_ = s;
  }

 private:
  std::unique_ptr<std::string> index_expression_;
};

class PcSymmSpec {
public:
  std::string name;
  std::string idx_name;
  std::string closed_assume_expression;
  std::string invariant_expression;
  LetVblMap let_map;

  Table<VblSymmAccessSpec> access;
  Table<uint> wmap;
  Table<LinkSymmetry> link_symmetries;
  std::string nmembs_expression;
  std::string idxmap_name;
  std::string idxmap_expression;
  Table<std::string> shadow_act_strings;
  Table<std::string> forbid_act_strings;
  Table<std::string> permit_act_strings;


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
  std::string closed_assume_expression;
  std::string invariant_expression;

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

