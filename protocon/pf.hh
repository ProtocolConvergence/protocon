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
  mdd_t* vMdd;
public:
  PF() : vMdd(0) {}

  PF(const PF& pf)
  {
    vMdd = pf.dup_mdd();
  }
  ~PF()
  {
    clear();
  }

  void defeq(mdd_t* a)
  {
    if (vMdd)  mdd_free(vMdd);
    vMdd = a;
  }

  const PF& operator=(const PF& pf)
  {
    defeq(mdd_dup(pf.vMdd));
    return *this;
  }

  bool equivCk(const PF& pf) const
  {
    if (!vMdd || !pf.vMdd) {
      return (!vMdd && !pf.vMdd);
    }
    return mdd_equal(vMdd, pf.vMdd);
  }


  PF operator~() const
  {
    PF pf;
    pf.defeq(mdd_not(vMdd));
    return pf;
  }

  PF operator-() const
  { return ~ *this; }

  PF operator!() const
  { return ~ *this; }

  const PF& operator&=(const PF& pf)
  {
    if (!vMdd)  return (*this = pf);
    defeq(mdd_and(vMdd, pf.vMdd, 1, 1));
    return *this;
  }

  PF operator&(const PF& pf) const
  {
    PF x;
    if (!vMdd)  return pf;
    x.defeq(mdd_and(vMdd, pf.vMdd, 1, 1));
    return x;
  }

  const PF& operator*=(const PF& pf)
  { return (*this &= pf); }

  PF operator*(const PF& pf) const
  { return (*this & pf); }

  PF operator&&(const PF& pf) const
  { return (*this & pf); }


  const PF& operator|=(const PF& pf)
  {
    if (!vMdd)  return (*this = pf);
    defeq(mdd_or(vMdd, pf.vMdd, 1, 1));
    return *this;
  }

  PF operator|(const PF& pf) const
  {
    PF x;
    if (!vMdd)  return pf;
    x.defeq(mdd_or(vMdd, pf.vMdd, 1, 1));
    return x;
  }

  const PF& operator+=(const PF& pf)
  { return (*this |= pf); }

  PF operator+(const PF& pf) const
  { return (*this | pf); }

  PF operator||(const PF& pf) const
  { return (*this | pf); }


  const PF& operator-=(const PF& pf)
  {
    if (!vMdd)  return (*this = pf);
    defeq(mdd_and(vMdd, pf.vMdd, 1, 0));
    return *this;
  }

  PF operator-(const PF& pf) const
  {
    PF x;
    if (!vMdd)  return pf;
    x.defeq(mdd_and(vMdd, pf.vMdd, 1, 0));
    return x;
  }


  /// Check if this is a tautology.
  bool tautologyCk(bool t = true) const {
    if (!vMdd)  return true;
    return mdd_is_tautology(vMdd, t ? 1 : 0);
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
    PF pf;
    pf.defeq(mdd_eq_c(vCtx, idx, val));
    return pf;
  }

  PF vbleq(uint idx1, uint idx2) const
  {
    PF pf;
    pf.defeq(mdd_eq(vCtx, idx1, idx2));
    return pf;
  }

  PF smooth(const PF& a, uint setIdx) const
  {
    PF b;
    b.defeq(mdd_smooth(vCtx, a.vMdd, vVblLists[setIdx]));
    return b;
  }

  PF substituteNewOld(const PF& a, uint newSetIdx, uint oldSetIdx) const
  {
    PF b;
    b.defeq(mdd_substitute(vCtx, a.vMdd, vVblLists[oldSetIdx], vVblLists[newSetIdx]));
    return b;
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

