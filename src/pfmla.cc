/**
 * \file pfmla.cc
 * This file has functions for the propositional formula data structure.
 */

#include "pfmla.hh"
#include "cx/map.hh"

namespace Cx {

/**
 * Perform backwards reachability.
 * \param pf  Initial states.
 */
  PFmla
PFmla::pre_reach(const P::Fmla& pf) const
{
  P::Fmla visit( pf );
  P::Fmla layer( this->pre(pf) - visit );
  while (layer.sat_ck()) {
    visit |= layer;
    layer = this->pre(layer) - visit;
  }
  return visit;
}

/**
 * Perform forward reachability.
 * \param pf  Initial states.
 */
  PFmla
PFmla::img_reach(const PFmla& pf) const
{
  P::Fmla visit( pf );
  P::Fmla layer( this->img(pf) - visit );
  while (layer.sat_ck()) {
    visit |= layer;
    layer = this->img(layer) - visit;
  }
  return visit;
}

/**
 * Compute a closed subset of some set of states.
 **/
  PFmla
PFmla::closure_within(const P::Fmla& pf) const
{
  return pf - this->pre_reach(~pf);
}

/**
 * Check for cycles within the entire state space.
 *
 * This uses a variant of the Emerson-Lei algorithm.
 * It simply computes a fixpoint of the transition relation by
 * iteratively computing the image until it does not change.
 */
  bool
PFmla::cycle_ck(P::Fmla* scc, uint* ret_nlayers, const P::Fmla* invariant, const P::Fmla* assumed) const
{
  const X::Fmla& xn = *this;
  P::Fmla span0( true, xn );
  if (assumed)
    span0 = *assumed;

  uint nlayers = 1;

  while (true) {
    const P::Fmla& span1 = xn.img(span0);
    if (span0.equiv_ck(span1))  break;
    if (ret_nlayers) {
      if (invariant && span0.subseteq_ck(*invariant)) {
        *ret_nlayers = nlayers;
        ret_nlayers = 0;
      }
      else {
        nlayers += 1;
        if (*ret_nlayers > 0 && nlayers > *ret_nlayers) {
          *ret_nlayers = nlayers;
          return false;
        }
      }
    }
    span0 = span1;
  }
  if (ret_nlayers)
    *ret_nlayers = nlayers;

  while (true) {
    const P::Fmla& span1 = span0 & xn.pre(span0);
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
PFmla::cycle_ck(P::Fmla* scc, const P::Fmla& pf) const
{
  return this->cycle_ck(scc, 0, 0, &pf);
}

/**
 * Check for cycles within some state predicate.
 */
  bool
PFmla::cycle_ck(const PFmla& pf) const
{
#if 0
  return SCC_Find(0, *this, pf);
#else
  return this->cycle_ck(0, pf);
#endif
}


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
PFmla::of_state(const uint* state, const Table<uint>& vbls, C::PFmlaCtx* ctx)
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
PFmla::of_img_state(const uint* state, const Table<uint>& vbls, C::PFmlaCtx* ctx)
{
  PFmla conj( true );
  PFmla pf;
  for (uint i = 0; i < vbls.sz(); ++i) {
    img_eqc_PFmlaVbl (&pf.g, vbl_of_PFmlaCtx (ctx, vbls[i]), state[i]);
    conj &= pf;
  }
  return conj;
}

  PFmla
PFmlaCtx::pfmla_of_state(const uint* state, const Table<uint>& vbls) const
{
  return PFmla::of_state(state, vbls, this->ctx);
}

  PFmla
PFmlaCtx::pfmla_of_img_state(const uint* state, const Table<uint>& vbls) const
{
  return PFmla::of_img_state(state, vbls, this->ctx);
}

static inline
  void
intmap_init_op (Table<uint>& vbl_map, IntPFmla& a, const IntPFmla& b)
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
                     zuint idx_a,
                     const Table<uint>& vbl_map,
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
  zuint idx_b = index_of_state (state_b, b.doms);

  return b.state_map[idx_b];
}

  IntPFmla&
IntPFmla::negate()
{
  zuint n = state_map.sz();
  for (zuint i = 0; i < n; ++i) {
    state_map[i] = - state_map[i];
  }
  return *this;
}

  IntPFmla&
IntPFmla::defeq_binop(const IntPFmla& b, IntPFmla::BinIntOp op)
{
  IntPFmla& a = *this;

  Table< uint > vbl_map( b.vbls.sz() );
  intmap_init_op (vbl_map, a, b);
  Table< uint > state_a( a.vbls.sz() );
  Table< uint > state_b( b.vbls.sz() );
  const zuint n = a.state_map.sz();

#define foreach_a for (zuint idx_a = 0; idx_a < n; ++idx_a)
#define val_a() a.state_map[idx_a]
#define val_b() intmap_coerce_lookup(a, b, idx_a, vbl_map, &state_a[0], &state_b[0])
  switch (op)
  {
  case IntPFmla::AddOp:
    foreach_a
      val_a() += val_b();
    break;
  case IntPFmla::SubOp:
    foreach_a
      val_a() -= val_b();
    break;
  case IntPFmla::MulOp:
    foreach_a
      val_a() *= val_b();
    break;
  case IntPFmla::DivOp:
    foreach_a {
      int x = val_b();
      Claim2( x ,!=, 0 );
      val_a() /= x;
    }
    break;
  case IntPFmla::ModOp:
    foreach_a {
      int x = val_b();
      Claim2( x ,>, 0 );
      val_a() = umod_int (val_a(), (uint) x);
    }
    break;
  case IntPFmla::PowOp:
    foreach_a {
      int x = val_b();
      Claim2( x ,>=, 0 );
      int val = 1;
      while (x > 0) {
        val *= val_a();
        x -= 1;
      }
      val_a() = val;
    }
    break;
  case IntPFmla::MinOp:
    foreach_a {
      int x = val_b();
      //int aa = val_a();
      if (x < val_a()) {
        val_a() = x;
      }
      //DBog3("min(%d %d)==%d", aa, x, val_a());
    }
    break;
  case IntPFmla::MaxOp:
    foreach_a {
      int x = val_b();
      //int aa = val_a();
      if (x > val_a()) {
        val_a() = x;
      }
      //DBog3("max(%d %d)==%d", aa, x, val_a());
    }
    break;
  case IntPFmla::NBinIntOps:
    Claim( 0 );
    break;
  }
#undef foreach_a
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

  Table< uint > vbl_map( b.vbls.sz() );
  intmap_init_op (vbl_map, a, b);
  Table< uint > state_a( a.vbls.sz() );
  Table< uint > state_b( b.vbls.sz() );
  const zuint n = a.state_map.sz();

  PFmla disj( false );
  for (zuint idx_a = 0; idx_a < n; ++idx_a) {
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

  Map< int, Table<luint> > inverse_a;
  Map< int, Table<luint> > inverse_b;
  for (zuint idx_a = 0; idx_a < a.state_map.sz(); ++idx_a) {
    inverse_a[a.state_map[idx_a]].push(idx_a);
  }
  for (zuint idx_b = 0; idx_b < b.state_map.sz(); ++idx_b) {
    inverse_b[b.state_map[idx_b]].push(idx_b);
  }

  PFmla disj( false );

  Table< uint > state_a( a.vbls.sz() );
  Table< uint > state_b( b.vbls.sz() );
  Map< int, Table<luint> >::const_iterator itb = inverse_b.begin();
  Map< int, Table<luint> >::iterator ita = inverse_a.lower_bound(itb->first);
  Map< int, Table<luint> >::key_compare compfun = inverse_a.key_comp();
  while (ita != inverse_a.end() && itb != inverse_b.end()) {
    if (compfun(ita->first,itb->first)) {
      ita = inverse_a.lower_bound(itb->first);
    }
    else if (compfun(itb->first,ita->first)) {
      itb = inverse_b.lower_bound(ita->first);
    }
    else {
      const Table<luint>& idcs_a = ita->second;
      const Table<luint>& idcs_b = itb->second;

      PFmla disj_a( false );
      PFmla disj_b( false );
      for (zuint i = 0; i < idcs_a.sz(); ++i) {
        state_of_index (&state_a[0], idcs_a[i], a.doms);
        disj_a |= PFmla::of_img_state(&state_a[0], a.vbls, a.ctx);
      }
      for (zuint i = 0; i < idcs_b.sz(); ++i) {
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

/**
 * Perform forward and backward reachability.
 * \param xn  Transition function.
 * \param pf  Initial states.
 */
  P::Fmla
UndirectedReachability(const X::Fmla& xn, const P::Fmla& pf)
{
  P::Fmla visit( pf );
  P::Fmla layer( (xn.pre(pf) | xn.img(pf)) - visit );
  while (layer.sat_ck()) {
    visit |= layer;
    layer = (xn.pre(layer) | xn.img(layer)) - visit;
  }
  return visit;
}

  P::Fmla
transitive_closure(const X::Fmla& xn)
{
  P::Fmla reach( false );
  P::Fmla next( xn );
  while (!reach.equiv_ck (next))
  {
    reach = next;
    next |= reach.dotjoin(reach);
  }
  return reach;
}

////// Linear SCC detection
static
  void
Skel_Forward(const P::Fmla& V, const X::Fmla& E, const P::Fmla& NODE,
             P::Fmla& FW, P::Fmla& S1, P::Fmla& NODE1)
{
  using Cx::PFmla;
  using Cx::Table;

  Table< PFmla > stack;

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
SCC_Find(P::Fmla* ret_cycles,
         const P::Fmla& V, const X::Fmla& E,
         const P::Fmla& S, const P::Fmla& NODE)
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
    const PFmla& NODE1 = E.pre(scc & S) & S1;
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
SCC_Find(P::Fmla* ret_cycles, const X::Fmla& E, const P::Fmla& pf)
{
  X::Fmla tmp_E = E;
  P::Fmla tmp_pf = pf;
  fill_ctx (tmp_E, tmp_pf);
  P::Fmla tmp_S( false, tmp_E );
  P::Fmla tmp_NODE( false, tmp_E );
  return SCC_Find(ret_cycles, tmp_pf, tmp_E, tmp_S, tmp_NODE);
}

