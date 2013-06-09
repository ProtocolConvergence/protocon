/**
 * \file pfmla.hh
 * This file has the propositional formula data structure.
 */
#ifndef PFmla_HH_
#define PFmla_HH_

#include "cx/synhax.hh"
#include "cx/alphatab.hh"

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
    init_PFmla (&g);
    wipe1_PFmla (&g, phase);
  }

  ~PFmla()
  {
    lose_PFmla (&g);
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

  /// Check if this is a tautology.
  bool tautology_ck(bool t = true) const
  {
    if (t)  return tautology_ck_PFmla (g);
    return unsat_ck_PFmla (g);
  }

  bool equiv_ck(const PFmla& pf) const
  {
    return equiv_ck_PFmla (g, pf.g);
  }


  bool overlap_ck(const PFmla& pf) const
  {
    return overlap_ck_PFmla (g, pf.g);
  }

  bool operator<=(const PFmla& pf) const
  {
    return subseteq_ck_PFmla (g, pf.g);
  }

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

  PFmla& operator*=(const PFmla& pf)
  { return (*this &= pf); }

  PFmla operator*(const PFmla& pf) const
  { return (*this & pf); }

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

  PFmla& operator+=(const PFmla& pf)
  { return (*this |= pf); }

  PFmla operator+(const PFmla& pf) const
  { return (*this | pf); }

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

  PFmla xnor(const PFmla& b) const
  {
    PFmla c;
    xnor_PFmla (&c.g, g, b.g);
    return c;
  }

  PFmla smooth(uint setIdx) const
  {
    PFmla b;
    smooth_vbls_PFmla (&b.g, g, setIdx);
    return b;
  }

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
};

class PFmlaVbl
{
private:
  C::PFmlaVbl vbl;
  bool primed;

public:
  PFmlaVbl(const String& _name, uint _domsz)
  {
    this->vbl.ctx = 0;
    this->vbl.id = 0;
    this->vbl.name = cons1_AlphaTab (_name.cstr());
    this->vbl.domsz = _domsz;
    this->primed = false;
  }

  PFmlaVbl(const C::PFmlaVbl& x)
  {
    this->vbl.ctx = x.ctx;
    this->vbl.id = x.id;
    this->vbl.name = dflt_AlphaTab ();
    copy_AlphaTab (&this->vbl.name, &x.name);
    this->vbl.img_name = dflt_AlphaTab ();
    copy_AlphaTab (&this->vbl.img_name, &x.img_name);
    this->vbl.domsz = x.domsz;
    this->primed = false;
  }

  ~PFmlaVbl()
  {
    lose_PFmlaVbl (&vbl);
  }

  PFmlaVbl prime() const
  {
    Claim( !primed );
    PFmlaVbl x = PFmlaVbl(this->vbl);
    x.primed = true;
    return x;
  }

  PFmla operator==(uint x) const
  {
    PFmla pf;
    if (primed) {
      img_eqlc_PFmlaVbl (&pf.g,
                         vbl_of_PFmlaCtx (vbl.ctx, vbl.id),
                         x);
    }
    else {
      eqlc_PFmlaVbl (&pf.g,
                     vbl_of_PFmlaCtx (vbl.ctx, vbl.id),
                     x);
    }
    return pf;
  }

  PFmla operator==(const PFmlaVbl& x) const
  {
    PFmla pf;
    if (primed) {
      Claim( !x.primed );
      img_eql_PFmlaVbl (&pf.g,
                        vbl_of_PFmlaCtx (vbl.ctx, vbl.id),
                        vbl_of_PFmlaCtx (vbl.ctx, x.vbl.id));
    }
    else if (x.primed) {
      img_eql_PFmlaVbl (&pf.g,
                        vbl_of_PFmlaCtx (vbl.ctx, x.vbl.id),
                        vbl_of_PFmlaCtx (vbl.ctx, vbl.id));
    }
    else {
      eql_PFmlaVbl (&pf.g,
                    vbl_of_PFmlaCtx (vbl.ctx, vbl.id),
                    vbl_of_PFmlaCtx (vbl.ctx, x.vbl.id));
    }
    return pf;
  }

  PFmla operator!=(uint x) const
  {
    return ~((*this) == x);
  }

  PFmla operator!=(const PFmlaVbl& x) const
  {
    return ~((*this) == x);
  }
};


class PFmlaCtx
{
private:
  C::PFmlaCtx* ctx;

public:
  PFmlaCtx()
  {
    ctx = make_GluPFmlaCtx ();
  }

  ~PFmlaCtx()
  {
    free_PFmlaCtx (ctx);
  }

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

  void commit_initialization();

  const PFmlaVbl vbl(uint id) const
  {
    return PFmlaVbl( *vbl_of_PFmlaCtx (ctx, id) );
  }

  const PFmlaVbl vbl(const String& s) const
  {
    return PFmlaVbl( *vbl_lookup_PFmlaCtx (ctx, s.cstr()) );
  }

  ostream& oput(ostream& of,
                const PFmla& a,
                uint setIdx,
                const String& pfx = "",
                const String& sfx = "") const;
};
}

typedef Cx::PFmla PF;
typedef Cx::PFmlaVbl PFVbl;
typedef Cx::PFmlaCtx PFCtx;

#endif

