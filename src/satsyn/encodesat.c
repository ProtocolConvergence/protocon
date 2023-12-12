#include "encodesat.h"
#include <fildesh/fildesh.h>

    BoolLit
dflt2_BoolLit(bool val, uint vbl)
{
  BoolLit x;
  x.val = (val ? 1 : 0);
  x.vbl = vbl;
  return x;
}

  CnfDisj
dflt_CnfDisj()
{
  CnfDisj disj = DEFAULT_CnfDisj;
  return disj;
}

    void
lose_CnfDisj(CnfDisj* clause)
{
  LoseTable( clause->lits );
}

    void
app_CnfDisj(CnfDisj* clause, bool b, uint vbl)
{
  PushTable( clause->lits, dflt2_BoolLit(b, vbl) );
}

    CnfFmla
dflt_CnfFmla()
{
  CnfFmla fmla = DEFAULT_CnfFmla;
  return fmla;
}

    void
lose_CnfFmla(CnfFmla* fmla)
{
  LoseTable( fmla->idcs );
  LoseTable( fmla->vbls );
  lose_BitTable(&fmla->vals);
}

    void
app_CnfFmla(CnfFmla* fmla, const CnfDisj* clause)
{
    const zuint off = fmla->vbls.sz;
    Claim2( fmla->vbls.sz ,==, fmla->vals.sz );
    PushTable( fmla->idcs, off );
    GrowTable( fmla->vbls, clause->lits.sz );
    grow_BitTable(&fmla->vals, clause->lits.sz);
    for (uint i = 0; i < clause->lits.sz; ++i) {
        BoolLit lit = clause->lits.s[i];
        if (lit.val)  set1_BitTable(fmla->vals, off+i);
        else          set0_BitTable(fmla->vals, off+i);
        fmla->vbls.s[off+i] = lit.vbl;
    }
}

  void
clause_of_CnfFmla (CnfDisj* clause, const CnfFmla* fmla, zuint i)
{
  const zuint bel = (i+1 < fmla->idcs.sz
                     ? fmla->idcs.s[i+1]
                     : fmla->vbls.sz);
  clause->lits.sz = 0;
  for (i = fmla->idcs.s[i]; i < bel; ++i)
    app_CnfDisj (clause,
                 test_BitTable (fmla->vals, i),
                 fmla->vbls.s[i]);
}


  Sign
cmp_XnSz(const XnSz* a, const XnSz* b)
{
  return (*a < *b ? -1 : (*a > *b ? 1 : 0));
}

  Sign
cmp_XnSz2(const XnSz2* a, const XnSz2* b)
{
  const Sign si = cmp_XnSz(&a->i, &b->i);
  return (si == 0
          ? cmp_XnSz(&a->j, &b->j)
          : si);
}


  CnfFmla
encode_sat(FMem_synsearch* tape)
{
  DeclTableT( XnInfo, struct { zuint idx; CnfDisj impl; } );
  DeclTableT( State, struct { TableT(XnSz) tx; TableT(XnSz) to; } );

  FildeshAlloc* alloc = open_FildeshAlloc();
  FildeshKV lstate_map[1] = {DEFAULT_FildeshKV};
  FildeshKV xnmap[1] = {DEFAULT_FildeshKV};
  FildeshKV pathmap[1] = {DEFAULT_FildeshKV};

  DeclTable( State, states );
  CnfFmla fmla[] = {DEFAULT_CnfFmla};
  DeclTable( XnInfo, xns );
  CnfDisj clause[] = {DEFAULT_CnfDisj};

  const XnSys* restrict sys = tape->sys;
  XnRule* g;
  TableT(XnSz)* may_rules;
  FildeshKV_id kvid;

  lstate_map->alloc = alloc;
  xnmap->alloc = alloc;
  pathmap->alloc = alloc;

  g = grow1_rules_synsearch(tape);
  may_rules = grow1_may_rules_synsearch(tape);

  may_rules->sz = 0;

  if (all_BitTable(sys->legit))
  {
    tape->stabilizing = true;
    CopyTable( tape->rules, sys->legit_rules );
    return *fmla;
  }
  else
  {
    Trit stabilizing = detect_strong_convergence(tape);
    if (stabilizing != May)
    {
      if (stabilizing == Yes)
        tape->stabilizing = true;
      if (stabilizing == Nil)
        DBog0( "Hint protocol has a livelock!" );
      -- tape->rules.sz;
      return *fmla;
    }
  }

  set_may_rules(tape, may_rules, g);
  synsearch_quicktrim_mayrules(tape, tape->rules.sz-1);
  synsearch_trim(tape);
  if (tape->stabilizing) {
    return *fmla;
  }

  for (uint i = 0; i < tape->rules.sz-1; ++i) {
    XnSz step = step_XnRule(&tape->rules.s[i], sys);
    PushTable( *may_rules, step );
  }
  tape->rules.sz = 1;
  g = &tape->rules.s[0];

  while (tape->xn_stk.sz > 0)
    back1_Xn(&tape->xns, &tape->xn_stk);

  AffyTable( states, sys->nstates );
  states.sz = sys->nstates;
  for (uint i = 0; i < states.sz; ++i) {
    InitTable( states.s[i].to );
    InitTable( states.s[i].tx );
  }

  fmla->nvbls = may_rules->sz;
  for (uint i = 0; i < may_rules->sz; ++i) {
    rule_XnSys(g, sys, may_rules->s[i]);
    add_XnRule(tape, g);
    for (uint j = 0; j < *TopTable(tape->xn_stk); ++j) {
      XnSz2 t;
      size_t* xnmap_v;
      TableElT(XnInfo)* xn;
      t.i = tape->xn_stk.s[tape->xn_stk.sz-2-j];
      t.j = *TopTable( tape->xns.s[t.i] );
      Claim2( t.i ,<, sys->nstates );
      Claim2( t.j ,<, sys->nstates );

      xnmap_v = (size_t*)lookup_value_FildeshKV(xnmap, &t, sizeof(t));
      if (!xnmap_v) {
        size_t idx = xns.sz;

        kvid = ensure_FildeshKV(xnmap, &t, sizeof(t));
        assign_at_FildeshKV(xnmap, kvid, &idx, sizeof(idx));

        xn = Grow1Table( xns );
        xn->idx = fmla->nvbls ++;
        xn->impl = dflt_CnfDisj();
        app_CnfDisj(&xn->impl, false, xn->idx);
        PushTable( states.s[t.j].tx, t.i );
        PushTable( states.s[t.i].to, t.j );
      }
      else {
        xn = &xns.s[*xnmap_v];
      }
      app_CnfDisj(&xn->impl, true, i);

      clause->lits.sz = 0;
      app_CnfDisj(clause, false, i);
      app_CnfDisj(clause, true, xn->idx);
      app_CnfFmla(fmla, clause);
    }
    back1_Xn(&tape->xns, &tape->xn_stk);

    for (uint qi = 0; qi < g->q.sz; ++qi) {
      g->q.s[qi] = 0;
    }

    {
      XnSz step = step_XnRule(g, sys);
      TableT(zuint)* rules;
      kvid = ensure_FildeshKV(lstate_map, &step, sizeof(step));
      rules = (TableT(zuint)*) value_at_FildeshKV(lstate_map, kvid);
      if (!rules) {
        rules = fildesh_allocate(TableT(zuint), 1, alloc);
        InitTable( *rules );
        assign_memref_at_FildeshKV(lstate_map, kvid, rules);
      }
      PushTable( *rules, i );
    }
  }

  for (uint i = 0; i < xns.sz; ++i) {
    CnfDisj* clause = &xns.s[i].impl;
    app_CnfFmla(fmla, clause);
    lose_CnfDisj(clause);
  }

  for (kvid = any_id_FildeshKV(lstate_map);
       !fildesh_nullid(kvid);
       kvid = any_id_FildeshKV(lstate_map))
  {
    TableT(zuint)* rules = (TableT(zuint)*) value_at_FildeshKV(lstate_map, kvid);
    for (uint i = 0; i < rules->sz; ++i) {
      for (uint j = 0; j < i; ++j) {
        clause->lits.sz = 0;
        app_CnfDisj(clause, false, rules->s[i]);
        app_CnfDisj(clause, false, rules->s[j]);
        app_CnfFmla(fmla, clause);
      }
    }
    LoseTable( *rules );
    remove_at_FildeshKV(lstate_map, kvid);
  }
  close_FildeshKV(lstate_map);

  for (uint i = 0; i < states.sz; ++i) {
    if (!test_BitTable(sys->legit, i))
    {
      TableElT(State)* state = &states.s[i];

      if (state->to.sz == 0)
        DBog0( "Illegit state without outgoing transitions!!!!" );

      /* Deadlock freedom clause.*/
      clause->lits.sz = 0;
      for (uint j = 0; j < state->to.sz; ++j) {
        XnSz2 t;
        size_t* xnmap_v;
        zuint idx;
        t.i = i;
        t.j = state->to.s[j];
        xnmap_v = (size_t*) lookup_value_FildeshKV(xnmap, &t, sizeof(t));
        assert(xnmap_v);
        idx = xns.s[*xnmap_v].idx;
        app_CnfDisj(clause, true, idx);
      }

      app_CnfFmla(fmla, clause);
    }

    for (uint j = 0; j < states.sz; ++j) {
      if (states.s[i].to.sz > 0 && states.s[j].tx.sz > 0)
      {
        XnSz2 xn;
        size_t idx = fmla->nvbls ++;
        xn.i = i;
        xn.j = j;

        kvid = ensure_FildeshKV(pathmap, &xn, sizeof(xn));
        assign_at_FildeshKV(pathmap, kvid, &idx, sizeof(idx));

        if (i == j)
        {
          clause->lits.sz = 0;
          app_CnfDisj(clause, false, idx);
          app_CnfFmla (fmla, clause);
        }
      }
    }
  }

  for (kvid = any_id_FildeshKV(pathmap);
       !fildesh_nullid(kvid);
       kvid = any_id_FildeshKV(pathmap))
  {
    CnfDisj path_clause[] = {DEFAULT_CnfDisj};
    XnSz2 p = *(XnSz2*) key_at_FildeshKV(pathmap, kvid);
    zuint p_ij = *(zuint*) value_at_FildeshKV(pathmap, kvid);
    TableElT(State) state = states.s[p.j];

    app_CnfDisj(path_clause, false, p_ij);

    for (uint k_idx = 0; k_idx < state.tx.sz; ++k_idx) {
      size_t* xnmap_v;
      size_t k = state.tx.s[k_idx];
      size_t q_ikj;
      if (k == p.i)
      {
        /* In this case, just let q_{ikj} = t_{ij}.*/
        xnmap_v = (size_t*) lookup_value_FildeshKV(xnmap, &p, sizeof(p));
        assert(xnmap_v);
        q_ikj = xns.s[*xnmap_v].idx;
      }
      else
      {
        XnSz2 xn;
        zuint p_ik, t_kj;

        xn.i = p.i;
        xn.j = k;
        xnmap_v = (size_t*) lookup_value_FildeshKV(xnmap, &xn, sizeof(xn));
        if (!xnmap_v)  continue;
        p_ik = *xnmap_v;

        xn.i = k;
        xn.j = p.j;
        xnmap_v = (size_t*) lookup_value_FildeshKV(xnmap, &xn, sizeof(xn));
        Claim( xnmap_v );
        t_kj = xns.s[*xnmap_v].idx;

        q_ikj = fmla->nvbls ++;
        /* We wish for (q_{ikj} == p_{ik} && t_{kj}).*/

        /* (q_{ikj} => p_{ik}) */
        clause->lits.sz = 0;
        app_CnfDisj(clause, false, q_ikj);
        app_CnfDisj(clause, true , p_ik );
        app_CnfFmla(fmla, clause);
        /* (q_{ikj} => t_{kj}) */
        clause->lits.sz = 0;
        app_CnfDisj(clause, false, q_ikj);
        app_CnfDisj(clause, true , t_kj );
        app_CnfFmla(fmla, clause);
        /* (p_{ik} && t_{kj} => q_{ikj}) */
        clause->lits.sz = 0;
        app_CnfDisj(clause, true , q_ikj);
        app_CnfDisj(clause, false, p_ik );
        app_CnfDisj(clause, false, t_kj );
        app_CnfFmla(fmla, clause);
      }

      /* (q_{ikj} => p_{ij}) */
      clause->lits.sz = 0;
      app_CnfDisj(clause, false, q_ikj);
      app_CnfDisj(clause, true , p_ij );
      app_CnfFmla(fmla, clause);

      app_CnfDisj(path_clause, true, q_ikj);
    }
    app_CnfFmla(fmla, path_clause);
    lose_CnfDisj(path_clause);
    remove_at_FildeshKV(pathmap, kvid);
  }

  /* Lose everything we can before running the solve.*/
  for (uint i = 0; i < states.sz; ++i) {
    LoseTable( states.s[i].tx );
    LoseTable( states.s[i].to );
  }
  LoseTable( states );
  close_FildeshKV(pathmap);
  close_FildeshKV(xnmap);
  LoseTable( xns );
  lose_CnfDisj(clause);
  close_FildeshAlloc(alloc);
  return *fmla;
}

