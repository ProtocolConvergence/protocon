/**
 * \file pfmla.hh
 * This file has the propositional formula data structure.
 */
#ifndef PF_HH_
#define PF_HH_

#include "cx/synhax.hh"

extern "C" {
#include "pfmla-glu.h"
#include "pfmla.h"
}

namespace C {
  using ::PFmla;
  using ::PFmlaVbl;
  using ::PFmlaCtx;
}

class PF;
class PFVbl;
class PFCtx;

class PF
{
  friend class PFCtx;
  friend class PFVbl;

private:
  C::PFmla g;

public:
  /** One should never call the default constructor.
   * It is here only for containers.
   * A propositional formula should be initialized to true, false,
   * or anything else before it is used in operations.
   */
  PF()
  {
    // Phase is uninitialized.
    // Actually, it's false.
    init_PFmla (&g);
  }

  PF(const PF& pf)
  {
    init_PFmla (&g);
    iden_PFmla (&g, pf.g);
  }

  explicit PF(bool phase)
  {
    init_PFmla (&g);
    wipe1_PFmla (&g, phase);
  }

  ~PF()
  {
    lose_PFmla (&g);
  }

  PF& operator=(const PF& pf)
  {
    iden_PFmla (&g, pf.g);
    return *this;
  }
  PF& operator=(bool b)
  {
    wipe1_PFmla (&g, b);
    return *this;
  }

  /// Check if this is a tautology.
  bool tautologyCk(bool t = true) const {
    if (t)  return tautology_ck_PFmla (g);
    return unsat_ck_PFmla (g);
  }

  bool equivCk(const PF& pf) const
  {
    return equiv_ck_PFmla (g, pf.g);
  }

  bool overlapCk(const PF& pf) const
  {
    return overlap_ck_PFmla (g, pf.g);
  }

  bool operator<=(const PF& pf) const
  {
    return subseteq_ck_PFmla (g, pf.g);
  }

  PF operator~() const
  {
    PF pf;
    not_PFmla (&pf.g, g);
    return pf;
  }

  PF operator-() const
  { return ~ *this; }

  PF operator!() const
  { return ~ *this; }

  PF& operator&=(const PF& pf)
  {
    and_PFmla (&g, g, pf.g);
    return *this;
  }

  PF operator&(const PF& b) const
  {
    PF c;
    and_PFmla (&c.g, g, b.g);
    return c;
  }

  PF& operator*=(const PF& pf)
  { return (*this &= pf); }

  PF operator*(const PF& pf) const
  { return (*this & pf); }

  PF operator&&(const PF& pf) const
  { return (*this & pf); }


  PF& operator|=(const PF& b)
  {
    or_PFmla (&g, g, b.g);
    return *this;
  }

  PF operator|(const PF& b) const
  {
    PF c;
    or_PFmla (&c.g, g, b.g);
    return c;
  }

  PF& operator+=(const PF& pf)
  { return (*this |= pf); }

  PF operator+(const PF& pf) const
  { return (*this | pf); }

  PF operator||(const PF& pf) const
  { return (*this | pf); }


  PF& operator-=(const PF& b)
  {
    nimp_PFmla (&g, g, b.g);
    return *this;
  }

  PF operator-(const PF& b) const
  {
    PF c;
    nimp_PFmla (&c.g, g, b.g);
    return c;
  }

  PF xnor(const PF& b) const
  {
    PF c;
    xnor_PFmla (&c.g, g, b.g);
    return c;
  }

  PF smooth(uint setIdx) const
  {
    PF b;
    smooth_vbls_PFmla (&b.g, g, setIdx);
    return b;
  }

  PF substituteNewOld(uint newSetIdx, uint oldSetIdx) const
  {
    PF b;
    subst_vbls_PFmla (&b.g, g, newSetIdx, oldSetIdx);
    return b;
  }

};

class PFVbl
{
private:
  C::PFmlaVbl vbl;

public:
  PFVbl(const string& _name, uint _domsz)
  {
    this->vbl.ctx = 0;
    this->vbl.id = 0;
    this->vbl.name = cons1_AlphaTab (_name.c_str());
    this->vbl.domsz = _domsz;
  }


  PFVbl(const C::PFmlaVbl& x)
  {
    this->vbl.ctx = x.ctx;
    this->vbl.id = x.id;
    this->vbl.name = dflt_AlphaTab ();
    copy_AlphaTab (&this->vbl.name, &x.name);
    this->vbl.domsz = x.domsz;
  }

  ~PFVbl()
  {
    lose_PFmlaVbl (&vbl);
  }

  PF operator==(uint x) const
  {
    PF pf;
    eqlc_PFmlaVbl (&pf.g,
                   vbl_of_PFmlaCtx (vbl.ctx, vbl.id),
                   x);
    return pf;
  }

  PF operator==(const PFVbl& x) const
  {
    PF pf;
    eql_PFmlaVbl (&pf.g,
                  vbl_of_PFmlaCtx (vbl.ctx, vbl.id),
                  vbl_of_PFmlaCtx (vbl.ctx, x.vbl.id));
    return pf;
  }

  PF operator!=(uint x) const
  {
    return ~((*this) == x);
  }

  PF operator!=(const PFVbl& x) const
  {
    return ~((*this) == x);
  }
};


class PFCtx
{
private:
  C::PFmlaCtx* ctx;

public:
  PFCtx()
  {
    ctx = make_GluPFmlaCtx ();
  }

  ~PFCtx()
  {
    free_PFmlaCtx (ctx);
  }

  uint addVbl(const string& name, uint domsz)
  {
    return add_vbl_PFmlaCtx (ctx, name.c_str(), domsz);
  }

  uint addVblList()
  {
    return add_vbl_list_PFmlaCtx (ctx);
  }

  void addToVblList(uint setIdx, uint vblIdx)
  {
    add_to_vbl_list_PFmlaCtx (ctx, setIdx, vblIdx);
  }

  void commitInitialization();

  const PFVbl vbl(uint id) const
  {
    return PFVbl( *vbl_of_PFmlaCtx (ctx, id) );
  }

  const PFVbl vbl(const string& s) const
  {
    return PFVbl( *vbl_lookup_PFmlaCtx (ctx, s.c_str()) );
  }

  ostream& oput(ostream& of,
                const PF& a,
                uint setIdx,
                const string& pfx = "",
                const string& sfx = "") const;
};

#endif

