/**
 * \file pf.hh
 * This file has the propositional formula data structure.
 */
#ifndef PF_HH_
#define PF_HH_

#include "synhax.hh"
#include "mdd.h"

class PF;
class PFVbl;
class PFCtx;

class PF
{
  friend class PFCtx;

private:
  bool vPhase;
  mdd_t* vMdd;

public:
  /** One should never call the default constructor.
   * It is here only for containers.
   * A propositional formula should be initialized to true, false,
   * or anything else before it is used in operations.
   */
  PF() :
    // This comment is intensional.
    //vPhase( false )
     vMdd( 0 )
  {}

  PF(const PF& pf) :
    vPhase( pf.vPhase )
  {
    vMdd = pf.dup_mdd();
  }

  explicit PF(bool phase) :
    vPhase( phase )
    , vMdd( 0 )
  {}

  explicit PF(mdd_t* a) : vPhase( true ), vMdd( a ) {}

  ~PF()
  {
    clear();
  }

  PF& defeq(mdd_t* a)
  {
    vPhase = true;
    if (vMdd)  mdd_free(vMdd);
    vMdd = a;
    return *this;
  }

  PF& operator=(const PF& pf)
  {
    if (!pf.vMdd) {
      clear(pf.vPhase);
      return *this;
    }
    return defeq(pf.dup_mdd());
  }
  PF& operator=(bool b)
  {
    clear(b);
    return *this;
  }

  /// Check if this is a tautology.
  bool tautologyCk(bool t = true) const {
    if (!vMdd)  return (vPhase == t);
    return mdd_is_tautology(vMdd, t);
  }

  bool equivCk(const PF& pf) const
  {
    if (!vMdd)  return pf.tautologyCk(vPhase);
    if (!pf.vMdd)  return tautologyCk(pf.vPhase);
    return mdd_equal(vMdd, pf.vMdd);
  }

  bool overlapCk(const PF& pf) const
  {
    return !(*this & pf).tautologyCk(false);
  }

  bool operator<=(const PF& pf) const
  {
    return pf.equivCk(pf | *this);
  }

  PF operator~() const
  {
    if (!vMdd)  return PF( !vPhase );
    return PF( mdd_not(vMdd) );
  }

  PF operator-() const
  { return ~ *this; }

  PF operator!() const
  { return ~ *this; }

  PF& operator&=(const PF& pf)
  {
    if (!vMdd) {
      if (vPhase)  *this = pf;
      return *this;
    }
    if (!pf.vMdd) {
      if (!pf.vPhase)  *this = pf;
      return *this;
    }
    return defeq(mdd_and(vMdd, pf.vMdd, 1, 1));
  }

  PF operator&(const PF& pf) const
  {
    if (!vMdd) {
      if (vPhase)  return pf;
      return *this;
    }
    if (!pf.vMdd) {
      if (!pf.vPhase)  return pf;
      return *this;
    }
    return PF( mdd_and(vMdd, pf.vMdd, 1, 1) );
  }

  PF& operator*=(const PF& pf)
  { return (*this &= pf); }

  PF operator*(const PF& pf) const
  { return (*this & pf); }

  PF operator&&(const PF& pf) const
  { return (*this & pf); }


  PF& operator|=(const PF& pf)
  {
    if (!vMdd) {
      if (!vPhase)  *this = pf; 
      return *this;
    }
    if (!pf.vMdd) {
      if (pf.vPhase)  *this = pf;
      return *this;
    }
    defeq(mdd_or(vMdd, pf.vMdd, 1, 1));
    return *this;
  }

  PF operator|(const PF& pf) const
  {
    if (!vMdd) {
      if (!vPhase)  return pf; 
      return *this;
    }
    if (!pf.vMdd) {
      if (pf.vPhase)  return pf;
      return *this;
    }
    return PF( mdd_or(vMdd, pf.vMdd, 1, 1) );
  }

  PF& operator+=(const PF& pf)
  { return (*this |= pf); }

  PF operator+(const PF& pf) const
  { return (*this | pf); }

  PF operator||(const PF& pf) const
  { return (*this | pf); }


  PF& operator-=(const PF& pf)
  {
    if (!vMdd) {
      if (vPhase)  *this = ~pf;
      return *this;
    }
    if (!pf.vMdd) {
      if (pf.vPhase)  clear(false);
      return *this;
    }
    defeq(mdd_and(vMdd, pf.vMdd, 1, 0));
    return *this;
  }

  PF operator-(const PF& pf) const
  {
    if (!vMdd) {
      if (vPhase)  return ~pf;
      return *this;
    }
    if (!pf.vMdd) {
      if (pf.vPhase)  return PF( false );
      return *this;
    }
    return PF( mdd_and(vMdd, pf.vMdd, 1, 0) );
  }


  mdd_t* dup_mdd() const
  {
    if (!vMdd)  return 0;
    return mdd_dup(vMdd);
  }

private:
  void clear() {
    if (vMdd) {
      mdd_free(vMdd);
      vMdd = 0;
    }
  }
  void clear(bool phase) {
    clear();
    vPhase = phase;
  }
};

class PFVbl
{
private:
  PFCtx* vCtx;
public:
  uint idx;
  string name;
  uint domsz;

public:
  PFVbl(PFCtx* ctx, uint _idx, const string& _name, uint _domsz) :
    vCtx(ctx)
    , idx(_idx)
    , name(_name)
    , domsz(_domsz)
  {}

  PFVbl(const string& _name, uint _domsz) :
    vCtx(0)
    , idx(0)
    , name(_name)
    , domsz(_domsz)
  {}


  PF operator==(uint x) const;
  PF operator==(const PFVbl& x) const;
};

class PFCtx
{
private:
  mdd_manager* vCtx;
  vector<PFVbl> vVbls;
  map<string,uint> vVblMap;
  vector<array_t*> vVblLists;

public:
  PFCtx() : vCtx(0)
  {
  }

  ~PFCtx()
  {
    for (uint i = 0; i < vVblLists.size(); ++i) {
      array_free(vVblLists[i]);
    }
    if (vCtx) {
      mdd_quit(vCtx);
    }
  }

  const PFVbl* add(const PFVbl& vbl)
  {
    if (MapLookup(vVblMap, vbl.name)) {
      DBog1( "There already exists a variable with name: %s", vbl.name.c_str() );
      return NULL;
    }

    uint idx = (uint) vVbls.size();
    vVblMap[vbl.name] = idx;
    vVbls.push_back(PFVbl(this, idx, vbl.name, vbl.domsz));
    return &vVbls[idx];
  }

  uint addVblList()
  {
    array_t*& a = Grow1(vVblLists);
    a = array_alloc(uint, 0);
    return vVblLists.size() - 1;
  }

  void addToVblList(uint setIdx, uint vblIdx)
  {
    array_insert_last(uint, vVblLists[setIdx], vblIdx);
  }

  void commitInitialization()
  {
    array_t* doms = array_alloc(uint, 0);
    array_t* names = array_alloc(char*, 0);
    for (uint i = 0; i < vVbls.size(); ++i) {
      const PFVbl& vbl = vVbls[i];
      array_insert_last(uint, doms, vbl.domsz);
      array_insert_last(const char*, names, vbl.name.c_str());
    }
    vCtx = mdd_init_empty();
    mdd_create_variables(vCtx, doms, names, 0);
    array_free(doms);
    array_free(names);
  }

  PF nil() const
  {
    PF pf;
    pf.defeq(mdd_zero(vCtx));
    return pf;
  }

  const PFVbl vbl(uint idx) const
  {
    return vVbls[idx];
  }

  const PFVbl vbl(const string& s) const
  {
    const uint* idx = MapLookup(vVblMap, s);
    // Live on the edge!
    //if (!idx)  return NULL;
    return vVbls[*idx];
  }

  PF vbleqc(uint idx, uint val) const
  {
    return PF( mdd_eq_c(vCtx, idx, val) );
  }

  PF vbleq(uint idx1, uint idx2) const
  {
    return PF( mdd_eq(vCtx, idx1, idx2) );
  }

  PF smooth(const PF& a, uint setIdx) const
  {
    if (!a.vMdd)  return a;
    return PF( mdd_smooth(vCtx, a.vMdd, vVblLists[setIdx]) );
  }

  PF substituteNewOld(const PF& a, uint newSetIdx, uint oldSetIdx) const
  {
    if (!a.vMdd)  return a;
    return PF( mdd_substitute(vCtx, a.vMdd, vVblLists[oldSetIdx], vVblLists[newSetIdx]) );
  }

  //bool subseteq(const PF& a, const PF& b, uint setIdx);

  mdd_manager* mdd_ctx() { return vCtx; }
};

inline PF PFVbl::operator==(uint x) const
{
  return vCtx->vbleqc(idx, x);
}

inline PF PFVbl::operator==(const PFVbl& x) const
{
  return vCtx->vbleq(idx, x.idx);
}

#endif

