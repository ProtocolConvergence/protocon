/**
 * \file pfmla.hh
 * This file has the propositional formula data structure.
 */
#ifndef PFmla_HH_
#define PFmla_HH_

#include "cx/synhax.hh"
#include "cx/alphatab.hh"
#include "cx/table.hh"

extern "C" {
#include "pfmla-glu.h"
#include "pfmla.h"
}

namespace Cx {
namespace C {
  using ::PFmla;
  using ::PFmlaVbl;
  using ::PFmlaCtx;
}

class PFmla;
class IntPFmla;
class PFmlaVbl;
class PFmlaCtx;

class PFmla
{
  friend class PFmlaCtx;
  friend class PFmlaVbl;

private:
  C::PFmla g;

public:
  /** One should never call the default constructor.
   * It is here only for containers.
   * A propositional formula should be initialized to true, false,
   * or anything else before it is used in operations.
   */
  PFmla()
  {
    // Phase is uninitialized.
    // Actually, it's false.
    init_PFmla (&g);
  }

  PFmla(const PFmla& pf)
  {
    init_PFmla (&g);
    iden_PFmla (&g, pf.g);
  }

  explicit PFmla(bool phase)
  {
    init1_PFmla (&g, phase);
  }

  PFmla(bool phase, const PFmla& pf)
  {
    init2_PFmla (&g, phase, pf.g);
  }

  ~PFmla()
  {
    lose_PFmla (&g);
  }

  friend void fill_ctx (PFmla&, PFmla&);

  void ensure_ctx (const PFmlaCtx& ctx);

  PFmla tautology(bool phase) const
  {
    PFmla a;
    a.g = cons1_PFmla (g->ctx, phase);
    return a;
  }

  PFmla& operator=(const PFmla& pf)
  {
    iden_PFmla (&g, pf.g);
    return *this;
  }
  PFmla& operator=(bool b)
  {
    wipe1_PFmla (&g, b);
    return *this;
  }

  bool sat_ck() const
  {
    return sat_ck_PFmla (this->g);
  }

  /// Check if this is a tautology.
  bool tautology_ck(bool t = true) const
  {
    if (t)  return tautology_ck_PFmla (g);
    return !this->sat_ck();
  }

  bool equiv_ck(const PFmla& pf) const
  {
    return equiv_ck_PFmla (g, pf.g);
  }


  bool overlap_ck(const PFmla& pf) const
  {
    return overlap_ck_PFmla (g, pf.g);
  }

  bool subseteq_ck(const PFmla& pf) const
  {
    return subseteq_ck_PFmla (g, pf.g);
  }
  bool operator<=(const PFmla& pf) const
  { return this->subseteq_ck(pf); }

  PFmla operator~() const
  {
    PFmla pf;
    not_PFmla (&pf.g, g);
    return pf;
  }

  PFmla operator-() const
  { return ~ *this; }

  PFmla operator!() const
  { return ~ *this; }

  PFmla& operator&=(const PFmla& pf)
  {
    and_PFmla (&g, g, pf.g);
    return *this;
  }

  PFmla operator&(const PFmla& b) const
  {
    PFmla c;
    and_PFmla (&c.g, g, b.g);
    return c;
  }

  PFmla operator&&(const PFmla& pf) const
  { return (*this & pf); }


  PFmla& operator|=(const PFmla& b)
  {
    or_PFmla (&g, g, b.g);
    return *this;
  }

  PFmla operator|(const PFmla& b) const
  {
    PFmla c;
    or_PFmla (&c.g, g, b.g);
    return c;
  }

  PFmla operator||(const PFmla& pf) const
  { return (*this | pf); }


  PFmla& operator-=(const PFmla& b)
  {
    nimp_PFmla (&g, g, b.g);
    return *this;
  }

  PFmla operator-(const PFmla& b) const
  {
    PFmla c;
    nimp_PFmla (&c.g, g, b.g);
    return c;
  }

  PFmla& defeq_xnor(const PFmla& b)
  {
    xnor_PFmla (&g, g, b.g);
    return *this;
  }
  PFmla xnor(const PFmla& b) const
  {
    PFmla c;
    xnor_PFmla (&c.g, g, b.g);
    return c;
  }

  PFmla& operator^=(const PFmla& b)
  {
    xor_PFmla (&g, g, b.g);
    return *this;
  }
  PFmla operator^(const PFmla& b) const
  {
    PFmla c;
    xor_PFmla (&c.g, g, b.g);
    return c;
  }

  PFmla smooth(uint setIdx) const
  {
    PFmla b;
    smooth_vbls_PFmla (&b.g, g, setIdx,  0);
    return b;
  }

  PFmla smooth_pre(uint setIdx) const
  {
    PFmla b;
    smooth_vbls_PFmla (&b.g, g, setIdx, -1);
    return b;
  }

  PFmla smooth_img(uint setIdx) const
  {
    PFmla b;
    smooth_vbls_PFmla (&b.g, g, setIdx,  1);
    return b;
  }

  PFmla smooth(const PFmlaVbl& vbl) const;

  PFmla substitute_new_old(uint newSetIdx, uint oldSetIdx) const
  {
    PFmla b;
    subst_vbls_PFmla (&b.g, g, newSetIdx, oldSetIdx);
    return b;
  }

  PFmla pre(const PFmla& img_arg) const
  {
    PFmla dst;
    pre1_PFmla (&dst.g, this->g, img_arg.g);
    return dst;
  }

  PFmla pre() const
  {
    PFmla dst;
    pre_PFmla (&dst.g, this->g);
    return dst;
  }

  PFmla img_as_img() const
  {
    PFmla dst;
    img_as_img_PFmla (&dst.g, this->g);
    return dst;
  }

  PFmla img(const PFmla& pre_arg) const
  {
    PFmla dst;
    img1_PFmla (&dst.g, this->g, pre_arg.g);
    return dst;
  }

  PFmla img() const
  {
    PFmla dst;
    img_PFmla (&dst.g, this->g);
    return dst;
  }

  PFmla pre_reach(const PFmla& pf) const;
  PFmla img_reach(const PFmla& pf) const;
  PFmla closure_within(const PFmla& pf) const;
  bool cycle_ck(PFmla* scc, uint* ret_nlayers = 0, const Cx::PFmla* invariant = 0) const;
  bool cycle_ck(PFmla* scc, const PFmla& pf) const;
  bool cycle_ck(const PFmla& pf) const;

  PFmla dotjoin(const PFmla& b) const
  {
    PFmla dst;
    dotjoin_PFmla (&dst.g, this->g, b.g);
    return dst;
  }

  PFmla inverse() const
  {
    PFmla dst;
    inverse_PFmla (&dst.g, this->g);
    return dst;
  }

  PFmla as_img() const
  {
    PFmla dst;
    as_img_PFmla (&dst.g, this->g);
    return dst;
  }

  /**
   * Pick a single satisfying instance.
   */
  PFmla pick_pre() const
  {
    PFmla dst;
    pick_pre_PFmla (&dst.g, this->g);
    return dst;
  }

  void state (uint* state, const Cx::Table<uint>& vbls) const
  {
    state_of_PFmla (state, this->g, &vbls[0], vbls.sz());
  }

  static PFmla of_state(const uint* state, const Cx::Table<uint>& vbls, C::PFmlaCtx* ctx);
  static PFmla of_img_state(const uint* state, const Cx::Table<uint>& vbls, C::PFmlaCtx* ctx);
};

inline
  void
fill_ctx (PFmla& a, PFmla& b)
{
  fill_ctx_PFmla (&a.g, &b.g);
}

class PFmlaVbl
{
public:
  const C::PFmlaVbl* x;

  PFmlaVbl() : x(0) {}

  PFmlaVbl(const C::PFmlaVbl* b) : x(b) {}

  PFmla operator==(uint b) const
  {
    PFmla pf;
    eqc_PFmlaVbl (&pf.g, x, b);
    return pf;
  }

  PFmla operator==(const PFmlaVbl& b) const
  {
    PFmla pf;
    eq_PFmlaVbl (&pf.g, x, b.x);
    return pf;
  }

  PFmla operator!=(uint b) const
  { return ~((*this) == b); }

  PFmla operator!=(const PFmlaVbl& b) const
  { return ~((*this) == b); }

  PFmla img_eq(uint b) const
  {
    PFmla pf;
    img_eqc_PFmlaVbl (&pf.g, x, b);
    return pf;
  }

  PFmla img_eq(const PFmlaVbl& b) const
  {
    PFmla pf;
    img_eq_PFmlaVbl (&pf.g, x, b.x);
    return pf;
  }

  PFmla img_eq(const IntPFmla& b) const;

  bool equiv_ck(const PFmlaVbl& b) const
  {
    return (x == b.x);
  }
};

inline uint id_of(const PFmlaVbl& vbl) { return vbl.x->id; }

inline
  PFmla
PFmla::smooth(const PFmlaVbl& vbl) const
{
  PFmla b;
  smooth_vbl_PFmla (&b.g, g, vbl.x, 0);
  return b;
}


class IntPFmla
{
private:
  enum BinIntOp {
    AddOp, SubOp,
    MulOp, DivOp, ModOp,
    PowOp,
    NBinIntOps
  };
public:
  C::PFmlaCtx* ctx;
  Cx::Table<uint> vbls; ///< Variable IDs.
  Cx::Table<uint> doms; ///< Domain sizes.
  Cx::Table<int> state_map;

  IntPFmla() : ctx(0) {}

  IntPFmla(const PFmlaVbl& x)
    : ctx(x.x->ctx)
  {
    vbls.push(x.x->id);
    doms.push(x.x->domsz);
    state_map.grow(x.x->domsz);
    for (uint i = 0; i < state_map.sz(); ++i) {
      state_map[i] = (int) i;
    }
  }

  IntPFmla(int x)
    : ctx(0)
  {
    state_map.push(x);
  }

  IntPFmla(int mul, int add, uint n)
    : ctx(0)
  {
    doms.push(n);
    state_map.grow(n);
    for (uint i = 0; i < n; ++i) {
      state_map[i] = (mul * (add + (int) i));
    }
  }

  IntPFmla& negate();

  IntPFmla& defeq_binop(const IntPFmla& b, BinIntOp op);

  IntPFmla& operator+=(const IntPFmla& b) { return this->defeq_binop(b, AddOp); }
  IntPFmla& operator-=(const IntPFmla& b) { return this->defeq_binop(b, SubOp); }
  IntPFmla& operator*=(const IntPFmla& b) { return this->defeq_binop(b, MulOp); }
  IntPFmla& operator/=(const IntPFmla& b) { return this->defeq_binop(b, DivOp); }
  IntPFmla& operator%=(const IntPFmla& b) { return this->defeq_binop(b, ModOp); }

  IntPFmla& defeq_pow(const IntPFmla& b)  { return this->defeq_binop(b, PowOp); }

  IntPFmla operator+(const IntPFmla& b) const { return IntPFmla(*this) += b; }
  IntPFmla operator-(const IntPFmla& b) const { return IntPFmla(*this) -= b; }
  IntPFmla operator*(const IntPFmla& b) const { return IntPFmla(*this) *= b; }
  IntPFmla operator/(const IntPFmla& b) const { return IntPFmla(*this) /= b; }
  IntPFmla operator%(const IntPFmla& b) const { return IntPFmla(*this) %= b; }

  PFmla cmp(const IntPFmla& b, Bit c_lt, Bit c_eq, Bit c_gt) const;

  PFmla operator< (const IntPFmla& b) const { return this->cmp(b, 1, 0, 0); }
  PFmla operator<=(const IntPFmla& b) const { return this->cmp(b, 1, 1, 0); }
  PFmla operator!=(const IntPFmla& b) const { return this->cmp(b, 1, 0, 1); }
  PFmla operator==(const IntPFmla& b) const { return this->cmp(b, 0, 1, 0); }
  PFmla operator>=(const IntPFmla& b) const { return this->cmp(b, 0, 1, 1); }
  PFmla operator> (const IntPFmla& b) const { return this->cmp(b, 0, 0, 1); }
  PFmla img_eq(const IntPFmla& b) const;
};

inline IntPFmla operator+(const PFmlaVbl& a, const IntPFmla& b) { return IntPFmla(a) += b; }
inline IntPFmla operator-(const PFmlaVbl& a, const IntPFmla& b) { return IntPFmla(a) -= b; }
inline IntPFmla operator*(const PFmlaVbl& a, const IntPFmla& b) { return IntPFmla(a) *= b; }
inline IntPFmla operator/(const PFmlaVbl& a, const IntPFmla& b) { return IntPFmla(a) /= b; }
inline IntPFmla operator%(const PFmlaVbl& a, const IntPFmla& b) { return IntPFmla(a) %= b; }

inline PFmla operator< (const PFmlaVbl& a, const IntPFmla& b) { return IntPFmla(a).cmp(b, 1, 0, 0); }
inline PFmla operator<=(const PFmlaVbl& a, const IntPFmla& b) { return IntPFmla(a).cmp(b, 1, 1, 0); }
inline PFmla operator!=(const PFmlaVbl& a, const IntPFmla& b) { return IntPFmla(a).cmp(b, 1, 0, 1); }
inline PFmla operator==(const PFmlaVbl& a, const IntPFmla& b) { return IntPFmla(a).cmp(b, 0, 1, 0); }
inline PFmla operator>=(const PFmlaVbl& a, const IntPFmla& b) { return IntPFmla(a).cmp(b, 0, 1, 1); }
inline PFmla operator> (const PFmlaVbl& a, const IntPFmla& b) { return IntPFmla(a).cmp(b, 0, 0, 1); }
inline PFmla PFmlaVbl::img_eq(const IntPFmla& b) const { return IntPFmla(*this).img_eq(b); }

class PFmlaCtx
{
private:
  C::PFmlaCtx* ctx;
  bool own_ctx;

public:
  PFmlaCtx()
    : ctx(0)
    , own_ctx(true)
  {
    ctx = make_GluPFmlaCtx ();
  }

  explicit PFmlaCtx(C::PFmlaCtx* _ctx)
    : ctx(_ctx)
    , own_ctx(true)
  {
  }

  ~PFmlaCtx()
  {
    if (ctx && own_ctx) {
      free_PFmlaCtx (ctx);
    }
  }

  void use_context_of(PFmlaCtx& a)
  {
    if (ctx && own_ctx) {
      free_PFmlaCtx (ctx);
    }
    own_ctx = false;
    ctx = a.ctx;
  }
  void nullify_context()
  { ctx = 0; }

  uint add_vbl(const String& name, uint domsz)
  {
    return add_vbl_PFmlaCtx (ctx, name.cstr(), domsz);
  }

  uint add_vbl_list()
  {
    return add_vbl_list_PFmlaCtx (ctx);
  }

  void add_to_vbl_list(uint setIdx, uint vblIdx)
  {
    add_to_vbl_list_PFmlaCtx (ctx, setIdx, vblIdx);
  }

  const PFmlaVbl vbl(uint id) const
  {
    return PFmlaVbl( vbl_of_PFmlaCtx (ctx, id) );
  }

  const PFmlaVbl vbl(const String& s) const
  {
    return PFmlaVbl( vbl_lookup_PFmlaCtx (ctx, s.cstr()) );
  }

  PFmla pfmla_of_state(const uint* state, const Cx::Table<uint>& vbls) const;
  PFmla pfmla_of_img_state(const uint* state, const Cx::Table<uint>& vbls) const;

  ostream& oput(ostream& of,
                const PFmla& a,
                uint setIdx,
                const String& pfx = "",
                const String& sfx = "") const;
  friend void PFmla::ensure_ctx (const PFmlaCtx& ctx);
};

inline
  void
PFmla::ensure_ctx (const PFmlaCtx& ctx)
{
  ensure_ctx_PFmla (&g, ctx.ctx);
}

}

Cx::PFmla
UndirectedReachability(const Cx::PFmla& xn, const Cx::PFmla& pf);
Cx::PFmla
transitive_closure(const Cx::PFmla& xn);
bool
SCC_Find(Cx::PFmla* ret_cycles, const Cx::PFmla& E, const Cx::PFmla& pf);

#endif

