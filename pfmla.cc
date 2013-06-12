/**
 * \file pfmla.cc
 * This file has functions for the propositional formula data structure.
 */

#include "pfmla.hh"

namespace Cx {

/**
 * Output all valuations of variables which satisfy a formula.
 *
 * \param of  Output stream.
 * \param a  The formula.
 * \param setIdx  Only print the variables in this set.
 * \param pfx  Prefix to output before every valuation.
 * \param sfx  Suffix to output after every valuation.
 **/
  ostream&
PFmlaCtx::oput(ostream& of, const PFmla& a, uint setIdx,
               const String& pfx, const String& sfx) const
{
  (void) a;
  (void) setIdx;
  of << pfx << "/*(NOT IMPLEMENTED)*/" << sfx;
#if 0
  mdd_gen* gen;
  array_t* minterm;
  array_t* vars = vVblLists[setIdx];
  foreach_mdd_minterm(a.vMdd, gen, minterm, vars) {
    of << pfx;
    for (uint i = 0; i < (uint) minterm->num; ++i) {
      uint x = array_fetch(uint, minterm, i);
      uint vidx = array_fetch(uint, vars, i);
      const PF::PFmlaVbl& vbl = vVbls[vidx];
      if (i > 0) {
        of << " && ";
      }
      of << vbl.name << "==" << x;
    }
    of << sfx;
    array_free(minterm);
  }
#endif
  return of;
}


  PFmla
PFmla::of_state(const uint* state, const Cx::Table<uint>& vbls, C::PFmlaCtx* ctx)
{
  PFmla conj( true );
  PFmla pf;
  for (uint i = 0; i < vbls.sz(); ++i) {
    eqlc_PFmlaVbl (&pf.g, vbl_of_PFmlaCtx (ctx, vbls[i]), state[i]);
    conj &= pf;
  }
  return conj;
}


static inline
  ujint
intmap_init_op (Cx::Table<uint>& vbl_map, IntPFmla& a, const IntPFmla& b)
{
  if (!a.ctx) {
    a.ctx = b.ctx;
  }
  else if (b.ctx) {
    Claim2( a.ctx ,==, b.ctx );
  }
  for (uint i = 0; i < b.doms.sz(); ++i) {
    bool found = false;
    for (uint j = 0; j < a.doms.sz(); ++j) {
      if (b.vbls[i] == a.vbls[j]) {
        found = true;
        vbl_map[i] = j;
        break;
      }
    }
    if (!found) {
      vbl_map[i] = a.vbls.sz();
      a.vbls.push(b.vbls[i]);
      a.doms.push(b.doms[i]);
      a.state_map.add_domain(b.doms[i]);
    }
  }

  ujint n = 1;
  for (uint i = 0; i < a.doms.sz(); ++i) {
    n *= a.doms[i];
  }
  return n;
}

static inline
  int
intmap_coerce_lookup(const IntPFmla& a,
                     const IntPFmla& b,
                     ujint idx_a,
                     const Cx::Table<uint>& vbl_map,
                     uint* state_a,
                     uint* state_b)
{
  state_of_index (state_a, idx_a, a.doms);

  for (uint j = 0; j < b.doms.sz(); ++j) {
    state_b[j] = state_a[vbl_map[j]];
  }
  ujint idx_b = index_of_state (state_b, b.doms);
  return b.state_map[idx_b];
}

  IntPFmla&
IntPFmla::defeq_binop(const IntPFmla& b, IntPFmla::BinIntOp op)
{
  IntPFmla& a = *this;

  Cx::Table< uint > vbl_map( b.doms.sz() );
  ujint n = intmap_init_op (vbl_map, a, b);
  Cx::Table< uint > state_a( a.doms.sz() );
  Cx::Table< uint > state_b( b.doms.sz() );

#define val_a() a.state_map[idx_a]
#define val_b() intmap_coerce_lookup(a, b, idx_a, vbl_map, &state_a[0], &state_b[0])
  switch (op)
  {
  case IntPFmla::AddOp:
    for (ujint idx_a = 0; idx_a < n; ++idx_a)
      val_a() += val_b();
    break;
  case IntPFmla::SubOp:
    for (ujint idx_a = 0; idx_a < n; ++idx_a)
      val_a() -= val_b();
    break;
  case IntPFmla::MulOp:
    for (ujint idx_a = 0; idx_a < n; ++idx_a)
      val_a() *= val_b();
    break;
  case IntPFmla::DivOp:
    for (ujint idx_a = 0; idx_a < n; ++idx_a) {
      int x = val_b();
      Claim2( x ,!=, 0 );
      val_a() /= x;
    }
    break;
  case IntPFmla::ModOp:
    for (ujint idx_a = 0; idx_a < n; ++idx_a) {
      int x = val_b();
      Claim2( x ,>, 0 );
      int y = val_a();
      if (y >= 0) {
        y = y % x;
      }
      else {
        y = x - ((- y) % x);
        if (x == y) {
          y = 0;
        }
      }
      val_a() = y;
    }
    break;
  case IntPFmla::NBinIntOps:
    Claim( 0 );
    break;
  }
#undef val_a
#undef val_b

  return a;
}


  PFmla
IntPFmla::cmp(const IntPFmla& b, Bit c_lt, Bit c_eq, Bit c_gt) const
{
  IntPFmla a( *this );

  Cx::Table< uint > vbl_map( b.doms.sz() );
  ujint n = intmap_init_op (vbl_map, a, b);
  Cx::Table< uint > state_a( a.doms.sz() );
  Cx::Table< uint > state_b( b.doms.sz() );

  PFmla disj( false );
  for (ujint idx_a = 0; idx_a < n; ++idx_a) {
    int x = intmap_coerce_lookup(a, b, idx_a, vbl_map, &state_a[0], &state_b[0]);

    if (false
        || ((c_lt != 0) && (a.state_map[idx_a] <  x))
        || ((c_eq != 0) && (a.state_map[idx_a] == x))
        || ((c_gt != 0) && (a.state_map[idx_a] >  x))
       )
    {
      disj |= PFmla::of_state(&state_a[0], a.vbls, a.ctx);
    }
  }
  return disj;
}

}

