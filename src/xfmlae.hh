
#ifndef XFmlae_HH_
#define XFmlae_HH_
#include "pfmla.hh"

namespace X {
using Cx::PFmlaCtx;
using Cx::Mem;
using Cx::Table;

class FmlaeCtx;
class Fmlae;

class FmlaeCtx
{
  friend class X::Fmlae;
  Mem<PFmlaCtx> ctx;
public:
  Table<uint> wvbl_list_ids;
  X::Fmla identity_xn;
  Table<X::Fmla> act_unchanged_xfmlas;

  FmlaeCtx(PFmlaCtx& _ctx)
    : ctx(&_ctx)
    , identity_xn(true)
  {}
  uint sz() const { return wvbl_list_ids.sz(); }
};

class Fmlae
{
private:
  const X::FmlaeCtx* ctx;
  Table<X::Fmla> fmlas;

public:
  Fmlae()
    : ctx(0)
  {}

  Fmlae(const X::FmlaeCtx* _ctx)
    : ctx(_ctx)
  {
    fmlas.affysz(ctx->sz(), X::Fmla(false));
  }

  uint sz() const { return fmlas.sz(); }
  const X::Fmla& operator[](uint i) const { return fmlas[i]; }
  X::Fmla& operator[](uint i) { return fmlas[i]; }

  X::Fmla xfmla() const {
    X::Fmla ret(false);
    for (uint i = 0; i < this->sz(); ++i) {
      if ((*this)[i].sat_ck()) {
        ret |= (*this)[i] & ctx->act_unchanged_xfmlas[i];
      }
    }
    return ret;
  }

  P::Fmla pre(uint i) const {
    return (*this)[i].pre();
  }
  P::Fmla pre() const {
    P::Fmla ret(false);
    for (uint i = 0; i < this->sz(); ++i) {
      ret |= this->pre(i);
    }
    return ret;
  }
  P::Fmla pre(uint i, const P::Fmla& pf) const {
    return (*this)[i].pre(pf, ctx->wvbl_list_ids[i]);
  }

  P::Fmla pre(const P::Fmla& pf) const
  {
    P::Fmla ret(false);
    for (uint i = 0; i < this->sz(); ++i) {
      ret |= (*this)[i].pre(pf, ctx->wvbl_list_ids[i]);
    }
    return ret;
  }

  P::Fmla img(uint i) const {
    return (*this)[i].img();
  }
  P::Fmla img() const {
    P::Fmla ret(false);
    for (uint i = 0; i < this->sz(); ++i) {
      ret |= this->img(i);
    }
    return ret;
  }
  P::Fmla img(uint i, const P::Fmla& pf) const {
    return (*this)[i].img(pf, ctx->wvbl_list_ids[i]);
  }

  P::Fmla img(const P::Fmla& pf) const
  {
    P::Fmla ret(false);
    for (uint i = 0; i < this->sz(); ++i) {
      ret |= (*this)[i].img(pf, ctx->wvbl_list_ids[i]);
    }
    return ret;
  }

  X::Fmlae& operator=(bool b) {
    for (uint i = 0; i < this->sz(); ++i)
      fmlas[i] = b;
    return *this;
  }

  X::Fmlae& operator&=(const X::Fmlae& xn) {
    for (uint i = 0; i < this->sz(); ++i)
      fmlas[i] &= xn.fmlas[i];
    return *this;
  }

  X::Fmlae& operator|=(const X::Fmlae& xn) {
    for (uint i = 0; i < this->sz(); ++i)
      fmlas[i] |= xn.fmlas[i];
    return *this;
  }

  X::Fmlae& operator-=(const X::Fmlae& xn) {
    for (uint i = 0; i < this->sz(); ++i)
      fmlas[i] -= xn.fmlas[i];
    return *this;
  }

  X::Fmla transitive_closure(const P::Fmla* initial = 0) const;
  bool cycle_ck(P::Fmla* scc,
                uint* ret_nlayers = 0,
                const P::Fmla* invariant = 0,
                const P::Fmla* assumed = 0) const;
  bool probabilistic_livelock_ck
    (P::Fmla* scc,
     const P::Fmla& assumed) const;
  bool probabilistic_livelock_ck
    (P::Fmla* scc,
     const P::Fmla& assumed,
     const X::Fmla& progress,
     const X::Fmla* global_xn = 0) const;
};
}

#endif

