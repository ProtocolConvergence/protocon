
#include "synsearch.h"
#include "promela.h"

static const bool DBog_WeakChk    = true;
static const bool DBog_AssertRule = true;
static const bool DBog_QuickTrim = false;
static const bool DBog_SearchStep = true;

#define AppDelta( a, s0, s1 )  ((a) + (s1) - (s0))

  FMem_do_XnSys
cons1_FMem_do_XnSys(const XnSys* sys)
{
  FMem_do_XnSys tape;
  const zuint n = sys->vbls.sz;

  tape.sys = sys;
  tape.vals = AllocT( XnDomSz, n);
  tape.fixed = cons2_BitTable( n, 0 );
  InitTable( tape.evs );
  GrowTable( tape.evs, n );
  tape.evs.sz = 0;
  return tape;
}

  void
lose_FMem_do_XnSys(FMem_do_XnSys* tape)
{
  if (tape->vals)  free(tape->vals);
  lose_BitTable(&tape->fixed);
  LoseTable(tape->evs);
}

  FMem_synsearch
cons1_FMem_synsearch(const XnSys* sys)
{
  FMem_synsearch tape;

  tape.stabilizing = false;
  tape.sys = sys;
  tape.livelock_tape = cons1_FMem_detect_livelock(&sys->legit);
  tape.convergence_tape = cons1_FMem_detect_convergence(&sys->legit);
  tape.dostates_tape = cons1_FMem_do_XnSys(sys);

  InitTable( tape.xns );
  GrowTable( tape.xns, sys->legit.sz );
  for (uint i = 0; i < tape.xns.sz; ++i) {
    InitTable( tape.xns.s[i] );
  }

  InitTable( tape.xn_stk );
  InitTable( tape.rules );
  InitTable( tape.may_rules );
  InitTable( tape.cmp_xn_stk );
  InitTable( tape.influence_order );
  tape.n_cached_rules = 0;
  tape.n_cached_may_rules = 0;
  tape.rule_nwvbls = 0;
  tape.rule_nrvbls = 0;
  for (uint i = 0; i < sys->pcs.sz; ++i) {
    uint nwvbls = sys->pcs.s[i].nwvbls;
    uint nrvbls = sys->pcs.s[i].vbls.sz;
    if (nwvbls > tape.rule_nwvbls)  tape.rule_nwvbls = nwvbls;
    if (nrvbls > tape.rule_nrvbls)  tape.rule_nrvbls = nrvbls;
  }

  InitTable( tape.legit_states );
  for (uint i = 0; i < sys->legit.sz; ++i) {
    if (test_BitTable(sys->legit, i))
      PushTable( tape.legit_states, i );
  }

  for (uint i = 0; i < sys->legit_rules.sz; ++i) {
    add_XnRule(&tape, &sys->legit_rules.s[i]);
  }

  InitTable( tape.legit_xns );
  EnsizeTable( tape.legit_xns, tape.legit_states.sz );
  for (uint i = 0; i < tape.legit_states.sz; ++i) {
    InitTable( tape.legit_xns.s[i] );
    CopyTable( tape.legit_xns.s[i], tape.xns.s[tape.legit_states.s[i]] );
  }

  for (uint i = 0; i < sys->legit_rules.sz; ++i) {
    back1_Xn(&tape.xns, &tape.xn_stk);
  }

  return tape;
}

  void
lose_FMem_synsearch(FMem_synsearch* tape)
{
  lose_FMem_detect_livelock(&tape->livelock_tape);
  lose_FMem_detect_convergence(&tape->convergence_tape);
  lose_FMem_do_XnSys(&tape->dostates_tape);

  for (uint i = 0; i < tape->xns.sz; ++i) {
    LoseTable( tape->xns.s[i] );
  }
  LoseTable( tape->xns );
  LoseTable( tape->xn_stk );

  for (uint i = 0; i < tape->n_cached_rules; ++i) {
    LoseTable( tape->rules.s[i].p );
    LoseTable( tape->rules.s[i].q );
  }
  LoseTable( tape->rules );

  for (uint i = 0; i < tape->n_cached_may_rules; ++i) {
    LoseTable( tape->may_rules.s[i] );
  }
  LoseTable( tape->may_rules );

  LoseTable( tape->cmp_xn_stk );

  LoseTable( tape->influence_order );

  LoseTable( tape->legit_states );

  for (uint i = 0; i < tape->legit_xns.sz; ++i) {
    LoseTable( tape->legit_xns.s[i] );
  }
  LoseTable( tape->legit_xns );
}

static
  void
recu_do_XnSys(BitTable* bt, const XnEVbl* a, uint n, XnSz step, XnSz bel)
{
  XnSz stepsz, bigstepsz;
  if (n == 0)
  {
    for (; step < bel; ++ step)
      set1_BitTable(*bt, step);
    return;
  }

  stepsz = a[0].vbl->stepsz;
  bigstepsz = stepsz * a[0].vbl->domsz;
  step += stepsz * a[0].val;

  for (; step < bel; step += bigstepsz)
    recu_do_XnSys(bt, a+1, n-1, step, step + stepsz);
}

  void
do_XnSys(FMem_do_XnSys* tape, BitTable bt)
{
  tape->evs.sz = 0;
  for (uint i = 0; i < tape->fixed.sz; ++i) {
    XnEVbl e;
    if (test_BitTable(tape->fixed, i))
    {
      e.val = tape->vals[i];
      e.vbl = &tape->sys->vbls.s[i];
      PushTable( tape->evs, e );
    }
  }

  recu_do_XnSys(&bt, tape->evs.s, tape->evs.sz, 0, bt.sz);
}

static
  void
recu_do_push_XnSys(TableT(XnSz)* t, const XnEVbl* a, uint n, XnSz step, XnSz bel)
{
  XnSz stepsz, bigstepsz;
  if (n == 0)
  {
    for (; step < bel; ++ step)
      PushTable( *t, step );
    return;
  }

  stepsz = a[0].vbl->stepsz;
  bigstepsz = stepsz * a[0].vbl->domsz;
  step += stepsz * a[0].val;

  for (; step < bel; step += bigstepsz)
    recu_do_push_XnSys(t, a+1, n-1, step, step + stepsz);
}

  void
do_push_XnSys(FMem_do_XnSys* tape, TableT(XnSz)* t)
{
  tape->evs.sz = 0;
  for (uint i = 0; i < tape->fixed.sz; ++i) {
    XnEVbl e;
    if (test_BitTable(tape->fixed, i))
    {
      e.val = tape->vals[i];
      e.vbl = &tape->sys->vbls.s[i];
      PushTable( tape->evs, e );
    }
  }

  recu_do_push_XnSys(t, tape->evs.s, tape->evs.sz, 0, tape->sys->legit.sz);
}


/** Check for livelock and deadlock freedom
 * along with fulfillment of the original protocol.
 *
 * It is assumed that all transitions in legit states are found in the
 * original protocol (we just check edge counts).
 **/
  Trit
detect_strong_convergence(FMem_synsearch* tape)
{
  if (detect_livelock(&tape->livelock_tape, tape->xns))  return Nil;

  for (uint i = 0; i < tape->xns.sz; ++i) {
    if (tape->xns.s[i].sz == 0)
      if (!test_BitTable(tape->sys->legit, i))
        return May;
  }

  if (!tape->sys->syn_legit)
    for (uint i = 0; i < tape->legit_states.sz; ++i) {
      XnSz s0 = tape->legit_states.s[i];
      if (tape->xns.s[s0].sz != tape->legit_xns.s[i].sz)
        return May;
    }

  return Yes;
}

  void
back1_Xn(TableT(Xns)* xns, TableT(XnSz)* stk)
{
  zuint n = *TopTable(*stk);
  zuint off = stk->sz - (n + 1);

  for (uint i = 0; i < n; ++i) {
    xns->s[stk->s[off + i]].sz -= 1;
  }

  stk->sz = off;
}


  XnSz
apply1_XnRule(const XnRule* g, const XnSys* sys, XnSz sidx)
{
  const XnPc* pc = &sys->pcs.s[g->pc];
  for (uint i = 0; i < g->q.sz; ++i) {
    XnSz stepsz = sys->vbls.s[pc->vbls.s[i]].stepsz;
    sidx = AppDelta( sidx,
                     stepsz * g->p.s[i],
                     stepsz * g->q.s[i] );
  }
  return sidx;
}

  void
add_XnRule(FMem_synsearch* tape, const XnRule* g)
{
  TableT(Xns)* xns = &tape->xns;
  TableT(XnSz)* stk = &tape->xn_stk;
  XnSz nadds = 0;
  XnSz sa, sb;
  DeclTable( XnSz, t );
  FMem_do_XnSys* fix = &tape->dostates_tape;

  nadds = stk->sz;

  for (uint i = 0; i < g->p.sz; ++i) {
    const XnPc* pc = &tape->sys->pcs.s[g->pc];
    uint vi = pc->vbls.s[i];
    fix->vals[vi] = g->p.s[i];
    set1_BitTable(fix->fixed, vi);
  }

  do_push_XnSys(fix, stk);

  for (uint i = 0; i < g->p.sz; ++i) {
    const XnPc* pc = &tape->sys->pcs.s[g->pc];
    uint vi = pc->vbls.s[i];
    set0_BitTable(fix->fixed, vi);
  }

  /* Overlay the table.*/
  t.s = &stk->s[nadds];
  t.sz = stk->sz - nadds;
  stk->sz = nadds;
  nadds = 0;

  Claim2( t.sz ,>, 0 );
  sa = t.s[0];
  sb = apply1_XnRule(g, tape->sys, sa);

  for (uint i = 0; i < t.sz; ++i) {
    bool add = true;
    XnSz s0 = t.s[i];
    XnSz s1 = AppDelta( s0, sa, sb );
    /* XnSz s1 = apply1_XnRule(g, tape->sys, s0); */
    TableT(XnSz)* src = &xns->s[s0];
    Claim2( s0 ,<, tape->sys->nstates );
    Claim2( s1 ,<, tape->sys->nstates );

    for (uint j = 0; j < src->sz; ++j) {
      if (src->s[j] == s1)
      {
        add = false;
        break;
      }
    }

    if (add)
    {
      PushTable( *src, s1 );
      t.s[nadds] = s0;
      ++ stk->sz;
      ++ nadds;
    }
  }

  PushTable( *stk, nadds );
}


static
  int
cmpi_XnSz(const void* pa, const void* pb)
{
  const XnSz a = *(XnSz*) pa;
  const XnSz b = *(XnSz*) pb;
  return ((a > b) ? +1 :
          (a < b) ? -1 :
          0);
}

#if 1
/** Only sort by the first member.**/
static
  int
cmpi_XnSz2(const void* pa, const void* pb)
{
  return cmpi_XnSz(&((XnSz2*)pa)->i, &((XnSz2*)pb)->i);
}
#endif

/**
 * Find the initial set of potential transition rules (actions).
 *
 * The procedure is:
 * - Ensure the existing protocol is closed.
 * - Add rules that have already been given.
 * - Add rules that do not include legitimate states in the source states.
 *   Unless either...
 *  - All legitimate source states are mapped to legitimate destination states
 *    in the legitimate protocol.
 *  - /syn_legit==true/ and all legitimate source states are mapped to
 *    legitimate destination states.
 **/
  void
set_may_rules(FMem_synsearch* tape, TableT(XnSz)* may_rules, XnRule* g)
{
  const XnSys* restrict sys = tape->sys;

  /* Ensure protocol is closed.*/
  for (uint i = 0; i < tape->legit_xns.sz; ++i) {
    const TableT(XnSz)* t = &tape->legit_xns.s[i];
    for (uint j = 0; j < t->sz; ++j) {
      if (!test_BitTable(sys->legit, t->s[j]))
      {
        DBog0( "Protocol breaks closure." );
        may_rules->sz = 0;
        return;
      }
    }
  }

  /* Note: Scrap variable /g/ is the most recent rule.*/
  /* Add preexisting rules.*/
  for (uint i = 0; i < tape->rules.sz - 1; ++i) {
    add_XnRule(tape, &tape->rules.s[i]);
    if (0 == *TopTable( tape->xn_stk ))
    {
      DBog0( "Redundant rule given!" );
      back1_Xn(&tape->xns, &tape->xn_stk);
    }
  }


  for (uint i = 0; i < sys->n_rule_steps; ++i) {
    /* XnSz rule_step = i; */
    XnSz rule_step = sys->n_rule_steps - 1 - i;

    bool add = true;
    bool test_selfloop = true;
    DeclTable( XnSz, t );

    rule_XnSys(g, sys, rule_step);
    Claim2( rule_step ,==, step_XnRule(g, sys) );

    add_XnRule(tape, g);

    t.sz = *TopTable( tape->xn_stk );
    t.s = &tape->xn_stk.s[tape->xn_stk.sz - 1 - t.sz];

    if (t.sz == 0)  add = false;

    if (add)
      for (uint j = 0; j < t.sz; ++j) {
        const XnSz s0 = t.s[j];
        const XnSz s1 = *TopTable( tape->xns.s[s0] );

        if (!test_BitTable(sys->legit, s0))
        {
          /* Ok, start state is illegitimate.*/
        }
        else if (sys->syn_legit)
        {
          if (!test_BitTable(sys->legit, s1))
            add = false;
        }
        else
          /* Do not add rules that cause
           * bad transitions from legit states.
           */
        {
          const XnSz* elt;
          XnSz legit_idx;

          test_selfloop = false;

          elt = (XnSz*)
            bsearch(&s0, tape->legit_states.s,
                    tape->legit_states.sz, sizeof(XnSz),
                    cmpi_XnSz);

          legit_idx = IdxEltTable( tape->legit_states, elt );

          elt = (XnSz*)
            bsearch(&s1,
                    tape->legit_xns.s[legit_idx].s,
                    tape->legit_xns.s[legit_idx].sz,
                    sizeof(XnSz),
                    cmpi_XnSz);

          if (!elt)
            add = false;
        }
        if (!add)  break;
      }

    if (add && test_selfloop)
    {
      const XnSz s0 = t.s[0];
      add = (s0 != tape->xns.s[s0].s[0]);
    }

    back1_Xn(&tape->xns, &tape->xn_stk);

    if (add)
      PushTable( *may_rules, rule_step );
  }
}

  XnRule*
grow1_rules_synsearch(FMem_synsearch* tape)
{
  XnRule* g = Grow1Table( tape->rules );
  if (tape->rules.sz > tape->n_cached_rules)
  {
    *g = cons2_XnRule(tape->rule_nrvbls,
                      tape->rule_nwvbls);
    tape->n_cached_rules = tape->rules.sz;
  }
  return g;
}

  TableT(XnSz)*
grow1_may_rules_synsearch(FMem_synsearch* tape)
{
  TableT(XnSz)* may_rules = Grow1Table( tape->may_rules );

  if (tape->may_rules.sz > tape->n_cached_may_rules)
  {
    InitTable( *may_rules );
    ++ tape->n_cached_may_rules;
  }

  return may_rules;
}

/**
 * Only allow self-disabling actions in /mayrules/.
 * The top of /tape->rules/ must be allocated for temp memory.
 **/
  void
synsearch_quicktrim_mayrules(FMem_synsearch* tape, XnSz nadded)
{
  const XnSys* sys = tape->sys;
  TableT(XnSz)* may_rules = TopTable( tape->may_rules );
  XnSz off = 0;
  XnRule* g0 = TopTable( tape->rules );

  for (uint i = 0; i < may_rules->sz; ++i) {
    XnSz rule_step = may_rules->s[i];
    bool add = true;

    rule_XnSys(g0, sys, rule_step);

    Claim2( nadded+1 ,<=, tape->rules.sz );

    if (add)
      for (uint j = 0; j < nadded; ++j) {
        XnRule* g1 = &tape->rules.s[tape->rules.sz-1-nadded+j];
        bool match = (g0->pc == g1->pc);

        if (match)
          for (uint k = 0; k < g0->p.sz - g0->q.sz; ++k) {
            match = (g0->p.s[k+g0->q.sz] == g1->p.s[k+g0->q.sz]);
            if (!match)  break;
          }

        if (match)
        {
          /* Can't have two actions with the same guard.*/
          match = true;
          for (uint k = 0; k < g0->q.sz; ++k) {
            match = (g0->q.s[k] == g1->p.s[k]);
            if (!match)  break;
          }
          add = !match;
          if (!add)  break;

          /* Remove actions that would not be self-disabling.*/
          match = true;
          for (uint k = 0; k < g0->q.sz; ++k) {
            match = (g0->p.s[k] == g1->p.s[k]);
            if (!match)  break;
          }
          add = !match;
          if (!add)  break;
        }
      }

    if (add)
    {
      may_rules->s[off] = may_rules->s[i];
      ++ off;
    }
    else if (false)
    {
      OFile* of = stderr_OFile();
      oput_cstr_OFile(of, "Pruned: ");
      oput_promela_XnRule(of, g0, sys);
      oput_char_OFile(of, '\n');
    }
  }
  if (DBog_QuickTrim)
    DBog1( "Removed:%lu", may_rules->sz - off );
  may_rules->sz = off;
}

/**
 * Trim rules at a new synsearch() depth.
 * Try adding each remaining potential action.
 * - If the action causes a livelock, discard it.
 * - If the action achieves strong convergence,
 *   return with /tape->stabilizing=true/.
 **/
  void
synsearch_trim(FMem_synsearch* tape)
{
  const XnSys* sys = tape->sys;
  TableT(XnSz)* may_rules = TopTable( tape->may_rules );
  XnRule* g = TopTable( tape->rules );

  /* Trim down the next possible steps.*/
  if (true)
  {
    XnSz off = 0;

    for (uint i = 0; i < may_rules->sz; ++i) {
      Trit stabilizing;
      XnSz rule_step = may_rules->s[i];
      bool tolegit = false;
      zuint nresolved = 0;

      rule_XnSys(g, sys, rule_step);
      add_XnRule(tape, g);

      stabilizing = detect_strong_convergence(tape);

      if (stabilizing == Yes)
      {
        tape->stabilizing = true;
        return;
      }

      /* Prune if the rule doesn't add any useful transitions.
       * Note: This is probably invalid if we assume weak fairness.
       */
      if (stabilizing == May)
      {
        DeclTable( XnSz, t );
        t.sz = *TopTable( tape->xn_stk );
        t.s = &tape->xn_stk.s[tape->xn_stk.sz - 1 - t.sz];

        Claim2( t.sz ,>, 0 );

        for (uint j = 0; j < t.sz; ++j) {
          const XnSz s0 = t.s[j];
          const XnSz s1 = *TopTable( tape->xns.s[s0] );

          /* Resolves a deadlock or
           * helps fulfill the original protocol.
           */
          if (tape->xns.s[s0].sz == 1 ||
              test_BitTable (sys->legit, s0))
          {
            /* TODO: Make this count extra(?)
             * if the reachable states from the destination
             * include a legit state.
             */
            ++ nresolved;
            if (test_BitTable(sys->legit, s1))  tolegit = true;
          }
        }

        if (nresolved == 0)
          stabilizing = Nil;
      }

      if (stabilizing == May)
      {
        XnSz2 p;
        p.i = nresolved;
        p.j = may_rules->s[i];
        if (tolegit)  p.i = sys->legit.sz + p.i;
        PushTable( tape->influence_order, p );

        may_rules->s[off] = may_rules->s[i];
        ++ off;
      }
      else if (false)
      {
        OFile* of = stderr_OFile();
        oput_cstr_OFile(of, "Pruned: ");
        oput_promela_XnRule(of, g, sys);
        oput_char_OFile(of, '\n');
      }

      back1_Xn(&tape->xns, &tape->xn_stk);
    }
    may_rules->sz = off;
  }

  {
    qsort(tape->influence_order.s,
          tape->influence_order.sz,
          sizeof(*tape->influence_order.s),
          cmpi_XnSz2);
    for (uint i = 0; i < tape->influence_order.sz; ++i) {
      /* XnSz idx = tape->influence_order.sz - 1 - i; */
      XnSz idx = i;
      may_rules->s[i] = tape->influence_order.s[idx].j;
    }
    tape->influence_order.sz = 0;
  }
}

  bool
synsearch_check_weak (FMem_synsearch* tape, XnSz* ret_nreqrules)
{
  const XnSys* sys = tape->sys;
  TableT(XnSz)* may_rules = TopTable( tape->may_rules );
  XnRule* g = TopTable( tape->rules );
  XnSz nreqrules = 0;

  /* Check that a weakly stabilizing protocol
   * exists with the rules we have left.
   */
  if (true)
  {
    bool weak = true;
    for (uint i = 0; i < may_rules->sz; ++i) {
      XnSz rule_step = may_rules->s[i];
      rule_XnSys(g, sys, rule_step);
      add_XnRule(tape, g);
    }

    weak = detect_convergence(&tape->convergence_tape, tape->xns);

    if (!tape->sys->syn_legit)
      for (uint i = 0; i < tape->legit_states.sz; ++i) {
        XnSz nout = tape->xns.s[tape->legit_states.s[i]].sz;
        if (nout != tape->legit_xns.s[i].sz)
          weak = false;
      }

    if (weak)
    {
      XnSz idx = tape->xn_stk.sz;
      tape->cmp_xn_stk.sz = 0;

      for (uint i = 0; i < may_rules->sz; ++i) {
        const XnSz n = tape->xn_stk.s[idx - 1];
        idx -= n + 1;
        for (uint j = 0; j < n + 1; ++j) {
          PushTable( tape->cmp_xn_stk, tape->xn_stk.s[idx+j] );
        }
      }
    }

    for (uint i = 0; i < may_rules->sz; ++i) {
      back1_Xn(&tape->xns, &tape->xn_stk);
    }

    if (!weak)
    {
      may_rules->sz = 0;
      if (DBog_WeakChk)
        DBog1( "Not weakly stabilizing at depth %u.",
               tape->may_rules.sz-1 );
      return false;
    }
  }

  /* Find rules that are necessary.*/
  if (true)
  {
    XnSz off = 0;
    XnSz stk_idx, cmp_stk_idx;

    /* Add all rules backwards, to find which are absolutely required.*/
    for (uint i = 0; i < may_rules->sz; ++i) {
      XnSz rule_step = may_rules->s[may_rules->sz - 1 - i];
      rule_XnSys(g, sys, rule_step);
      add_XnRule(tape, g);
    }

    stk_idx = tape->xn_stk.sz;
    cmp_stk_idx = tape->cmp_xn_stk.sz;

    for (uint i = 0; i < may_rules->sz; ++i) {
      bool required = false;
      const XnSz nas = tape->xn_stk.s[stk_idx-1];
      const XnSz nbs = tape->cmp_xn_stk.s[cmp_stk_idx-1];
      const XnSz* as;
      const XnSz* bs;

      stk_idx -= nas + 1;
      cmp_stk_idx -= nbs + 1;

      as = &tape->xn_stk.s[stk_idx];
      bs = &tape->cmp_xn_stk.s[cmp_stk_idx];

      for (uint j = 0; j < nas; ++j) {
        const XnSz s0 = as[j];
        for (uint k = 0; k < nbs; ++k) {
          if (s0 == bs[k] &&
              tape->xns.s[s0].sz == 1 &&
              !(sys->syn_legit && test_BitTable(sys->legit, s0)))
          {
            required = true;
            j = nas;
            k = nbs;
          }
        }
      }

      tape->cmp_xn_stk.sz -= nbs + 1;

      if (required)
      {
        rule_XnSys(g, sys, may_rules->s[i]);
        g = grow1_rules_synsearch(tape);
        ++ nreqrules;
      }
      else
      {
        may_rules->s[off] = may_rules->s[i];
        ++ off;
      }
    }

    for (uint i = 0; i < may_rules->sz; ++i) {
      back1_Xn(&tape->xns, &tape->xn_stk);
    }

    may_rules->sz = off;
    Claim2( tape->cmp_xn_stk.sz ,==, 0 );
  }

  *ret_nreqrules = nreqrules;
  return true;
}

/**
 * TODO: Make sure this works when the protocol has
 * transitions defined in the legit states.
 **/
  void
synsearch(FMem_synsearch* tape)
{
  const XnSys* restrict sys = tape->sys;
  XnRule* g;
  XnSz nreqrules = 0;
  TableT(XnSz)* may_rules;

  g = grow1_rules_synsearch(tape);
  may_rules = grow1_may_rules_synsearch(tape);

  may_rules->sz = 0;

  if (tape->may_rules.sz == 1)
  {
    Trit stabilizing;
    if (all_BitTable(sys->legit))
    {
      tape->stabilizing = true;
      CopyTable( tape->rules, sys->legit_rules );
      return;
    }

    stabilizing = detect_strong_convergence(tape);
    if (Yes == stabilizing)
    {
      tape->stabilizing = true;
      -- tape->rules.sz;
      return;
    }
    if (stabilizing == Nil)
    {
      DBog0( "Hint protocol has a livelock!" );
      -- tape->rules.sz;
      return;
    }
    set_may_rules(tape, may_rules, g);
    synsearch_quicktrim_mayrules(tape, tape->rules.sz-1);
  }
  else
  {
    CopyTable( *may_rules, *(may_rules - 1) );
    synsearch_quicktrim_mayrules(tape, 1);
  }

  synsearch_trim(tape);
  if (tape->stabilizing)  return;

  while (may_rules->sz > 0)
  {
    if (!synsearch_check_weak(tape, &nreqrules))  break;
    g = TopTable( tape->rules );

    if (nreqrules > 0)
    {
      Trit stabilizing = May;
      -- tape->rules.sz;
      g = g - nreqrules;
      if (DBog_AssertRule)
        DBog3( "Assert %u/%u rules at depth %u.",
               nreqrules,
               may_rules->sz + nreqrules,
               tape->may_rules.sz-1 );
      for (uint i = 0; i < nreqrules; ++i) {
        add_XnRule(tape, g + i);
      }

      /* If the number of required rules is greater than 1,
       * we haven't checked its validity.
       */
      if (nreqrules > 1)
      {
        stabilizing = detect_strong_convergence (tape);

        if (stabilizing == Yes)
        {
          tape->stabilizing = true;
          return;
        }
      }

      if (stabilizing == May)
      {
        g = grow1_rules_synsearch(tape);
        synsearch_quicktrim_mayrules(tape, nreqrules);
        -- tape->rules.sz;
        g = TopTable( tape->rules );
        synsearch(tape);
        if (tape->stabilizing)  return;
      }

      for (uint i = 0; i < nreqrules; ++i) {
        back1_Xn(&tape->xns, &tape->xn_stk);
      }
      break;
    }
    else
    {
      XnSz rule_step = *TopTable( *may_rules );
      -- may_rules->sz;
      rule_XnSys(g, sys, rule_step);

      add_XnRule(tape, g);
      if (DBog_SearchStep
          || tape->may_rules.sz-1 < 40)
      {
        OFile* of = stderr_OFile();
        oput_cstr_OFile(of, " -- ");
        oput_uint_OFile(of, tape->may_rules.sz - 1);
        oput_cstr_OFile(of, " -- ");
        oput_uint_OFile(of, may_rules->sz);
        oput_cstr_OFile(of, " -- ");
        oput_promela_XnRule(of, g, sys);
        oput_char_OFile(of, '\n');
        flush_OFile(of);
      }

      synsearch(tape);
      if (tape->stabilizing)  return;
      back1_Xn(&tape->xns, &tape->xn_stk);

      g = TopTable( tape->rules );
      may_rules = TopTable( tape->may_rules );
    }
  }

  if (nreqrules > 0)  tape->rules.sz -= nreqrules;
  else                -- tape->rules.sz;

  -- tape->may_rules.sz;
  /* if (tape->rules.sz == 58)  exit(1); */
}
