/**
 * \file pfmla.cc
 * This file has functions for the propositional formula data structure.
 */

#include "pfmla.hh"
#include "cx/map.hh"

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
    eqc_PFmlaVbl (&pf.g, vbl_of_PFmlaCtx (ctx, vbls[i]), state[i]);
    conj &= pf;
  }
  return conj;
}

  PFmla
PFmla::of_img_state(const uint* state, const Cx::Table<uint>& vbls, C::PFmlaCtx* ctx)
{
  PFmla conj( true );
  PFmla pf;
  for (uint i = 0; i < vbls.sz(); ++i) {
    img_eqc_PFmlaVbl (&pf.g, vbl_of_PFmlaCtx (ctx, vbls[i]), state[i]);
    conj &= pf;
  }
  return conj;
}

static inline
  void
intmap_init_op (Cx::Table<uint>& vbl_map, IntPFmla& a, const IntPFmla& b)
{
  Claim2( a.state_map.sz() ,>, 0 );
  Claim2( b.state_map.sz() ,>, 0 );

  if (a.vbls.sz() == 0 && b.vbls.sz() == 0) {
    Claim( !a.ctx );
    Claim( !b.ctx );

    for (uint i = 0; i < b.doms.sz(); ++i) {
      a.doms.push(b.doms[i]);
    }
    // This is equivalent to adding each domain individually.
    a.state_map.add_domain(b.state_map.sz());
    return;
  }
  Claim2( a.vbls.sz() ,==, a.doms.sz() );
  Claim2( b.vbls.sz() ,==, b.doms.sz() );
  if (!a.ctx) {
    a.ctx = b.ctx;
  }
  Claim( a.ctx );
  //Claim2( a.vbls.sz() ,>, 0 );
  if (b.ctx) {
    Claim2( a.ctx ,==, b.ctx );
  }

  for (uint i = 0; i < b.vbls.sz(); ++i) {
    bool found = false;
    for (uint j = 0; j < a.vbls.sz(); ++j) {
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
  if (a.vbls.sz() == 0) {
    return b.state_map[idx_a % b.state_map.sz()];
  }
  state_of_index (state_a, idx_a, a.doms);

  for (uint j = 0; j < b.doms.sz(); ++j) {
    state_b[j] = state_a[vbl_map[j]];
  }
  ujint idx_b = index_of_state (state_b, b.doms);

  return b.state_map[idx_b];
}

  IntPFmla&
IntPFmla::negate()
{
  ujint n = state_map.sz();
  for (ujint i = 0; i < n; ++i) {
    state_map[i] = - state_map[i];
  }
  return *this;
}

  IntPFmla&
IntPFmla::defeq_binop(const IntPFmla& b, IntPFmla::BinIntOp op)
{
  IntPFmla& a = *this;

  Cx::Table< uint > vbl_map( b.vbls.sz() );
  intmap_init_op (vbl_map, a, b);
  Cx::Table< uint > state_a( a.vbls.sz() );
  Cx::Table< uint > state_b( b.vbls.sz() );
  const ujint n = a.state_map.sz();

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
      val_a() = umod_int (val_a(), (uint) x);
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

  if (a.vbls.sz() == 0 && b.vbls.sz() == 0) {
    // Not sure if sets make sense here.
    Claim2( a.state_map.sz() ,==, 1 );
    Claim2( b.state_map.sz() ,==, 1 );
  }

  Cx::Table< uint > vbl_map( b.vbls.sz() );
  intmap_init_op (vbl_map, a, b);
  Cx::Table< uint > state_a( a.vbls.sz() );
  Cx::Table< uint > state_b( b.vbls.sz() );
  const ujint n = a.state_map.sz();

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

  PFmla
IntPFmla::img_eq(const IntPFmla& b) const
{
  const IntPFmla& a = *this;
  if (a.vbls.sz() == 0) {
    return (a == b);
  }

  Cx::Map< int, Cx::Table<ujint> > inverse_a;
  Cx::Map< int, Cx::Table<ujint> > inverse_b;
  for (ujint idx_a = 0; idx_a < a.state_map.sz(); ++idx_a) {
    inverse_a[a.state_map[idx_a]].push(idx_a);
  }
  for (ujint idx_b = 0; idx_b < b.state_map.sz(); ++idx_b) {
    inverse_b[b.state_map[idx_b]].push(idx_b);
  }

  PFmla disj( false );

  Cx::Table< uint > state_a( a.vbls.sz() );
  Cx::Table< uint > state_b( b.vbls.sz() );
  Cx::Map< int, Cx::Table<ujint> >::const_iterator itb = inverse_b.begin();
  Cx::Map< int, Cx::Table<ujint> >::iterator ita = inverse_a.lower_bound(itb->first);
  Cx::Map< int, Cx::Table<ujint> >::key_compare compfun = inverse_a.key_comp();
  while (ita != inverse_a.end() && itb != inverse_b.end()) {
    if (compfun(ita->first,itb->first)) {
      ita = inverse_a.lower_bound(itb->first);
    }
    else if (compfun(itb->first,ita->first)) {
      itb = inverse_b.lower_bound(ita->first);
    }
    else {
      const Cx::Table<ujint>& idcs_a = ita->second;
      const Cx::Table<ujint>& idcs_b = itb->second;

      PFmla disj_a( false );
      PFmla disj_b( false );
      for (ujint i = 0; i < idcs_a.sz(); ++i) {
        state_of_index (&state_a[0], idcs_a[i], a.doms);
        disj_a |= PFmla::of_img_state(&state_a[0], a.vbls, a.ctx);
      }
      for (ujint i = 0; i < idcs_b.sz(); ++i) {
        state_of_index (&state_b[0], idcs_b[i], b.doms);
        disj_b |= PFmla::of_state(&state_b[0], b.vbls, b.ctx);
      }
      disj |= (disj_a & disj_b);

      ++ita;
      ++itb;
    }
  }

  return disj;
}

}


  PF
ClosedSubset(const PF& xnRel, const PF& invariant)
{
  return invariant - BackwardReachability(xnRel, ~invariant);
}

/**
 * Perform forward reachability.
 * \param xn  Transition function.
 * \param pf  Initial states.
 */
  Cx::PFmla
ForwardReachability(const Cx::PFmla& xn, const Cx::PFmla& pf)
{
  Cx::PFmla visit( pf );
  Cx::PFmla layer( xn.img(pf) - visit );
  while (layer.sat_ck()) {
    visit |= layer;
    layer = xn.img(layer) - visit;
  }
  return visit;
}

/**
 * Perform backwards reachability.
 * \param xnRel  Transition function.
 * \param pf  Initial states.
 */
  PF
BackwardReachability(const PF& xnRel, const PF& pf)
{
  PF visitPF( pf );
  PF layerPF( xnRel.pre(pf) - visitPF );
  while (layerPF.sat_ck()) {
    visitPF |= layerPF;
    layerPF = xnRel.pre(layerPF) - visitPF;
  }
  return visitPF;
}

/**
 * Perform forward and backward reachability.
 * \param xn  Transition function.
 * \param pf  Initial states.
 */
  Cx::PFmla
UndirectedReachability(const Cx::PFmla& xn, const Cx::PFmla& pf)
{
  Cx::PFmla visit( pf );
  Cx::PFmla layer( (xn.pre(pf) | xn.img(pf)) - visit );
  while (layer.sat_ck()) {
    visit |= layer;
    layer = (xn.pre(layer) | xn.img(layer)) - visit;
  }
  return visit;
}

  Cx::PFmla
transitive_closure(const Cx::PFmla& xn)
{
  Cx::PFmla reach( false );
  Cx::PFmla next( xn );
  while (!reach.equiv_ck (next))
  {
    reach = next;
    next |= reach.dotjoin(reach);
  }
  return reach;
}

  bool
cycle_ck (Cx::PFmla* scc, const Cx::PFmla& xn)
{
  Cx::PFmla span0( true );

  while (true) {
    const Cx::PFmla& span1 = xn.img(span0);
    if (span0.equiv_ck(span1))  break;
    span0 = span1;
  }

  while (true) {
    const Cx::PFmla& span1 = span0 & xn.pre(span0);
    if (span0.equiv_ck(span1))  break;
    span0 = span1;
  }

  if (scc)
    *scc = span0;

  return span0.sat_ck();
}

/**
 * Check for cycles within some state predicate.
 *
 * This uses a variant of the Emerson-Lei algorithm.
 * It simply computes a fixpoint of the transition relation by
 * iteratively computing the image until it does not change.
 */
  bool
cycle_ck(PF* scc, const PF& xn, const PF& pf)
{
  PF span0( true );

  while (true) {
    const PF& span1 = xn.img(span0);

    if (!pf.overlap_ck(span1))  return false;
    if (span0.equiv_ck(span1))  break;

    span0 = span1;
  }

  while (true) {
    const PF& span1 = span0 & xn.pre(span0);

    if (!pf.overlap_ck(span1))  return false;
    if (span0.equiv_ck(span1))  break;

    span0 = span1;
  }

  if (scc) {
    *scc = span0;
  }
  return true;
}

/**
 * Check for cycles within some state predicate.
 */
  bool
cycle_ck(const PF& xn, const PF& pf)
{
#if 0
  return SCC_Find(0, xn, pf);
#else
  return cycle_ck(0, xn, pf);
#endif
}

////// Linear SCC detection
static
  void
Skel_Forward(const Cx::PFmla& V, const Cx::PFmla& E, const Cx::PFmla& NODE,
             Cx::PFmla& FW, Cx::PFmla& S1, Cx::PFmla& NODE1)
{
  using Cx::PFmla;

  Cx::Table< PFmla > stack;

  PFmla level( NODE );
  FW = false;

  // Compute the forward set and push onto /stack/.
  while (level.sat_ck())
  {
    stack.push(level);
    FW |= level;
    level = (V & E.img(level)) - FW;
  }

  // Determine a skeleton of the forward set.
  level = stack.top();
  stack.mpop(1);
  NODE1 = level.pick_pre();
  S1 = NODE1;
  while (stack.sz() != 0) {
    level = stack.top();
    stack.mpop(1);
    S1 |= (E.pre(S1) & level).pick_pre();
  }
}

static
  bool
SCC_Find(Cx::PFmla* ret_cycles,
         const Cx::PFmla& V, const Cx::PFmla& E,
         const Cx::PFmla& S, const Cx::PFmla& NODE)
{
  const bool only_one_cycle = false;
  using Cx::PFmla;

  if (!V.sat_ck())
    return false;

  // Determine the node for which the SCC is computed.
  PFmla scc;
  if (!S.sat_ck())
    scc = V.pick_pre();
  else
    scc = NODE;

  PFmla FW;
  PFmla NewS;
  PFmla NewNODE;

  // Compute the forward-set of the vertex in NODE together with a skeleton.
  Skel_Forward(V, E, scc, FW, NewS, NewNODE);

  // Determine the SCC containing NODE.
  bool found = false;
  for (PFmla pf = (E.pre(scc) & FW);
       (pf - scc).sat_ck();
       pf = (E.pre(scc) & FW))
  {
    if (!ret_cycles)  return true;
    found = true;
    scc |= pf;
  }

  // Insert the SCC in the partition.
  if (found)
    *ret_cycles |= scc;

  if (found && only_one_cycle)  return true;

  // First recursive call: Computation of the SCCs in V - FW.
  {
    const PFmla& V1 = V - FW;
    // No reason to modify the E relation since we always AND the results
    // of E.img() or E.pre() with the vertex set V (or subsets of it).
    //const PFmla& E1 = (E & V1) & V1.as_img();
    const PFmla& S1 = S - scc;
    const PFmla& NODE1 = E.pre(scc | S) & (S - scc);
    const bool just_found =
      SCC_Find(ret_cycles, V1, E, S1, NODE1);

    found = found || just_found;
    if (found && !ret_cycles)
      return true;
    if (found && only_one_cycle)  return true;
  }

  // Second recursive call: Computation of the SCCs in FW - SCC
  {
    const PFmla& V1 = FW - scc;
    // No reason to modify the E relation since we always AND the results
    // of E.img() or E.pre() with the vertex set V (or subsets of it).
    //const PFmla& E1 = (E & V1) & V1.as_img();
    const PFmla& S1 = NewS - scc;
    const PFmla& NODE1 = NewNODE - scc;
    const bool just_found =
      SCC_Find(ret_cycles, V1, E, S1, NODE1);

    found = found || just_found;
  }

  return found;
}

/**
 * Find cycles in a linear number of symbolic steps as per the algorithm given by
 * by Gentilini, Piazza, and Policriti in their 2003 paper
 * "Computing strongly connected components in a linear number of symbolic steps".
 *
 * Even though it is theoretically linear, I have found the Emerson-Lei algorithm
 * to be faster.
 *
 * \sa CycleCk()
 */
  bool
SCC_Find(Cx::PFmla* ret_cycles, const Cx::PFmla& E, const Cx::PFmla& pf)
{
  Cx::PFmla tmp_E = E;
  Cx::PFmla tmp_pf = pf;
  Cx::PFmla tmp_S( false );
  Cx::PFmla tmp_NODE( false );
  fill_ctx (tmp_E, tmp_pf);
  fill_ctx (tmp_E, tmp_S);
  fill_ctx (tmp_E, tmp_NODE);
  return SCC_Find(ret_cycles, tmp_pf, tmp_E, tmp_S, tmp_NODE);
}

