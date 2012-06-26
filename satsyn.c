
#include "cx/bittable.h"
#include "cx/fileb.h"
#include "cx/sys-cx.h"
#include "cx/table.h"

#include <assert.h>
#include <stdio.h>

typedef struct XnPc XnPc;
typedef struct XnVbl XnVbl;
typedef struct XnEVbl XnEVbl;
typedef struct XnRule XnRule;
typedef struct XnSys XnSys;
typedef BitTableSz XnSz;
typedef byte DomSz;
typedef struct Disj3 Disj3;
typedef struct XnSz2 XnSz2;
typedef struct FnWMem_detect_livelock FnWMem_detect_livelock;
typedef struct FnWMem_detect_convergence FnWMem_detect_convergence;
typedef struct FnWMem_do_XnSys FnWMem_do_XnSys;
typedef struct FnWMem_synsearch FnWMem_synsearch;

DeclTableT( XnPc, XnPc );
DeclTableT( XnVbl, XnVbl );
DeclTableT( XnEVbl, XnEVbl );
DeclTableT( XnRule, XnRule );
DeclTableT( XnSz, XnSz );
DeclTableT( Disj3, Disj3 );
DeclTableT( Xns, TableT(XnSz) );
DeclTableT( XnSz2, XnSz2 );
DeclTableT( DomSz, DomSz );


struct XnSz2 { XnSz i; XnSz j; };

struct XnPc
{
    TableT(XnSz) vbls;
    XnSz nwvbls;
    XnSz nrvbls;

    XnSz rule_step;
    TableT(XnSz) rule_stepsz_p;
    TableT(XnSz) rule_stepsz_q;
};

struct XnVbl
{
    TableT(char) name;
    DomSz max;
    TableT(XnSz) pcs;
    XnSz nwpcs;
    XnSz nrpcs;
    XnSz stepsz;  /* In global state space.*/
};

struct XnEVbl
{
    DomSz val;  /* Evaluation.*/
    const XnVbl* vbl;
};

struct XnRule
{
    uint pc;
    TableT(DomSz) p;
    TableT(DomSz) q;
};

struct XnSys
{
    TableT(XnPc) pcs;
    TableT(XnVbl) vbls;
    BitTable legit;
    TableT(XnRule) legit_rules;
    XnSz nstates;  /* Same as /legit.sz/.*/
    XnSz n_rule_steps;
};

struct FnWMem_detect_livelock
{
    BitTable cycle;
    BitTable tested;
    TableT(XnSz2) testing;
    const BitTable* legit;
};

struct FnWMem_detect_convergence
{
    const BitTable* legit;
    TableT(Xns) bxns;
    TableT(XnSz) reach;
    BitTable tested;
};

struct FnWMem_do_XnSys
{
    DomSz* vals;
    BitTable fixed;
    TableT(XnEVbl) evs;
    const XnSys* sys;
};

struct FnWMem_synsearch
{
    bool stabilizing;
    const XnSys* sys;
    FnWMem_detect_livelock livelock_tape;
    FnWMem_detect_convergence convergence_tape;
    FnWMem_do_XnSys dostates_tape;
    TableT(Xns) xns;
    TableT(XnSz) xn_stk;
    TableT(XnRule) rules;
    TableT(Xns) may_rules;
    TableT(XnSz) cmp_xn_stk;
    uint n_cached_rules;
    uint n_cached_may_rules;
    uint rule_nwvbls;
    uint rule_nrvbls;
    TableT(XnSz) legit_states;
    TableT(Xns) legit_xns;
};

struct Disj3 {
    int terms[3];
};

    XnPc
dflt_XnPc ()
{
    XnPc pc;
    InitTable( pc.vbls );
    pc.nwvbls = 0;
    pc.nrvbls = 0;
    pc.rule_step = 0;
    InitTable( pc.rule_stepsz_p );
    InitTable( pc.rule_stepsz_q );
    return pc;
}

void
add_XnRule (FnWMem_synsearch* tape, const XnRule* g);

    void
lose_XnPc (XnPc* pc)
{
    LoseTable( pc->vbls );
    LoseTable( pc->rule_stepsz_p );
    LoseTable( pc->rule_stepsz_q );
}

    XnVbl
dflt_XnVbl ()
{
    XnVbl x;
    InitTable( x.name );
    SizeTable( x.name, 2 );
    x.name.s[0] = 'x';
    x.name.s[1] = '\0';
    x.max = 0;
    InitTable( x.pcs );
    x.nwpcs = 0;
    x.nrpcs = 0;
    x.stepsz = 0;
    return x;
}

    void
lose_XnVbl (XnVbl* x)
{
    LoseTable( x->name );
    LoseTable( x->pcs );
}

    XnRule
dflt_XnRule ()
{
    XnRule g;
    g.pc = 0;
    InitTable( g.p );
    InitTable( g.q );
    return g;
}

    XnRule
cons2_XnRule (uint np, uint nq)
{
    XnRule g = dflt_XnRule ();
    EnsizeTable( g.p, np );
    EnsizeTable( g.q, nq );
    { BLoop( i, np )
        g.p.s[i] = 0;
    } BLose()
    { BLoop( i, nq )
        g.q.s[i] = 0;
    } BLose()
    return g;
}

    void
lose_XnRule (XnRule* g)
{
    LoseTable( g->p );
    LoseTable( g->q );
}

    XnSys
dflt_XnSys ()
{
    XnSys sys;
    InitTable( sys.pcs );
    InitTable( sys.vbls );
    sys.legit = dflt_BitTable ();
    InitTable( sys.legit_rules );
    sys.nstates = 0;
    sys.n_rule_steps = 0;
    return sys;
}

    void
lose_XnSys (XnSys* sys)
{
    { BLoop( i, sys->pcs.sz )
        lose_XnPc (&sys->pcs.s[i]);
    } BLose()
    LoseTable( sys->pcs );
    { BLoop( i, sys->vbls.sz )
        lose_XnVbl (&sys->vbls.s[i]);
    } BLose()
    LoseTable( sys->vbls );
    lose_BitTable (&sys->legit);
    { BLoopT( XnSz, i, sys->legit_rules.sz )
        lose_XnRule (&sys->legit_rules.s[i]);
    } BLose()
    LoseTable( sys->legit_rules );
}

qual_inline
    void
dump_BitTable (OFileB* f, const BitTable bt)
{
    BitTableSz i;
    UFor( i, bt.sz )
        dump_char_OFileB (f, test_BitTable (bt, i) ? '1' : '0');
}


    TableT(XnSz)
wvbls_XnPc (XnPc* pc)
{
    DeclTable( XnSz, t );
    t.s = pc->vbls.s;
    t.sz = pc->nwvbls;
    return t;
}

    TableT(XnSz)
rvbls_XnPc (XnPc* pc)
{
    DeclTable( XnSz, t );
    t.s = &pc->vbls.s[pc->vbls.sz - pc->nrvbls];
    t.sz = pc->nrvbls;
    return t;
}

    TableT(XnSz)
wpcs_XnVbl (XnVbl* x)
{
    DeclTable( XnSz, t );
    t.s = x->pcs.s;
    t.sz = x->nwpcs;
    return t;
}

    TableT(XnSz)
rpcs_XnVbl (XnVbl* x)
{
    DeclTable( XnSz, t );
    t.s = &x->pcs.s[x->pcs.sz - x->nrpcs];
    t.sz = x->nrpcs;
    return t;
}

    XnSz
size_XnSys (const XnSys* sys)
{
    XnSz sz = 1;

    { BLoop( i, sys->vbls.sz )
        const XnSz psz = sz;
        sz *= (XnSz) sys->vbls.s[i].max + 1;

        if (sz <= psz)
        {
            fprintf (stderr, "Size shrunk!\n");
            return 0;
        }
    } BLose()

    return sz;
}

    /**
     * mode:
     *   Nil - write-only
     *   Yes - read-write
     *   May - read-only
     **/
    void
assoc_XnSys (XnSys* sys, uint pc_idx, uint vbl_idx, Trit mode)
{
    XnPc* const pc = &sys->pcs.s[pc_idx];
    XnVbl* const x = &sys->vbls.s[vbl_idx];

    if (mode == May)
    {
        PushTable( pc->vbls, vbl_idx );
        PushTable( x->pcs, pc_idx );
    }
    else
    {
        GrowTable( pc->vbls, 1 );
        GrowTable( x->pcs, 1 );

        { BLoop( i, pc->nrvbls )
            pc->vbls.s[pc->vbls.sz-i-1] =
                pc->vbls.s[pc->vbls.sz-i-2];
        } BLose()

        { BLoop( i, x->nrpcs )
            x->pcs.s[x->pcs.sz-i-1] =
                x->pcs.s[x->pcs.sz-i-2];
        } BLose()

        pc->vbls.s[pc->nwvbls ++] = vbl_idx;
        x->pcs.s[x->nwpcs ++] = pc_idx;
    }

    if (mode != Nil)
    {
        pc->nrvbls ++;
        x->nrpcs ++;
    }
}

    /** Call this when you're done specifying all processes and variables
     * and wish to start specifying invariants.
     **/
    void
accept_topology_XnSys (XnSys* sys)
{
    XnSz stepsz = 1;
    { BLoop( i, sys->vbls.sz )
        XnVbl* x = &sys->vbls.s[sys->vbls.sz-1-i];
        x->stepsz = stepsz;
        stepsz *= (1 + x->max);
        if (x->max != 0 && x->stepsz >= stepsz)
        {
            DBog0( "Cannot hold all the states!" );
            fail_exit_sys_cx (0);
        }
    } BLose()

        /* All legit states.*/
    sys->legit = cons2_BitTable (stepsz, 1);

    { BLoop( pcidx, sys->pcs.sz )
        XnPc* pc = &sys->pcs.s[pcidx];
        uint n;

        SizeTable( pc->rule_stepsz_p, pc->nrvbls );
        SizeTable( pc->rule_stepsz_q, pc->nwvbls );

        stepsz = 1;

        n = pc->rule_stepsz_q.sz;
        { BLoop( i, n )
            XnSz* x = &pc->rule_stepsz_q.s[n-1-i];
            DomSz max = sys->vbls.s[pc->vbls.s[n-1-i]].max;

            *x = stepsz;
            stepsz *= (1 + max);
            if (max != 0 && *x >= stepsz)
            {
                DBog0( "Cannot hold all the rules!" );
                fail_exit_sys_cx (0);
            }
        } BLose()

        n = pc->rule_stepsz_p.sz;
        { BLoop( i, n )
            XnSz* x = &pc->rule_stepsz_p.s[n-1-i];
            DomSz max = sys->vbls.s[pc->vbls.s[n-1-i]].max;

            *x = stepsz;
            stepsz *= (1 + max);
            if (max != 0 && *x >= stepsz)
            {
                DBog0( "Cannot hold all the rules!" );
                fail_exit_sys_cx (0);
            }
        } BLose()


        if (pcidx == 0)
            pc->rule_step = 0;

        sys->n_rule_steps = pc->rule_step + stepsz;

        if (pcidx < sys->pcs.sz-1)
            sys->pcs.s[pcidx+1].rule_step = sys->n_rule_steps;
    } BLose()
}


    void
dump_XnEVbl (OFileB* of, const XnEVbl* ev, const char* delim)
{
    dump_cstr_OFileB (of, ev->vbl->name.s);
    if (!delim)  delim = "=";
    dump_cstr_OFileB (of, delim);
    dump_uint_OFileB (of, ev->val);
}

    void
dump_promela_state_XnSys (OFileB* of, const XnSys* sys, XnSz sidx)
{
    { BLoop( i, sys->vbls.sz )
        XnEVbl x;
        x.vbl = &sys->vbls.s[i];
        x.val = sidx / x.vbl->stepsz;
        sidx = sidx % x.vbl->stepsz;
        if (i > 0)  dump_cstr_OFileB (of, " && ");
        dump_XnEVbl (of, &x, "==");
    } BLose()
}

    void
rule_XnSys (XnRule* g, const XnSys* sys, XnSz idx)
{
    const XnPc* pc = 0;
    g->pc = sys->pcs.sz - 1;
    { BLoop( i, sys->pcs.sz-1 )
        if (idx < sys->pcs.s[i+1].rule_step)
        {
            g->pc = i;
            break;
        }
    } BLose()

    pc = &sys->pcs.s[g->pc];
    idx -= pc->rule_step;

    EnsizeTable( g->p, pc->rule_stepsz_p.sz );
    { BLoop( i, g->p.sz )
        XnSz d = pc->rule_stepsz_p.s[i];
        g->p.s[i] = idx / d;
        idx = idx % d;
    } BLose()

    EnsizeTable( g->q, pc->rule_stepsz_q.sz );
    { BLoop( i, g->q.sz )
        XnSz d = pc->rule_stepsz_q.s[i];
        g->q.s[i] = idx / d;
        idx = idx % d;
    } BLose()
}


    void
dump_promela_XnRule (OFileB* of, const XnRule* g, const XnSys* sys)
{
    bool had;
    XnPc* pc = &sys->pcs.s[g->pc];
    TableT(XnSz) t;
    dump_cstr_OFileB (of, "/*P");
    dump_uint_OFileB (of, g->pc);
    dump_cstr_OFileB (of, "*/ ");

    t = rvbls_XnPc (pc);
    had = false;
    { BLoop( i, sys->vbls.sz )
        { BLoop( j, t.sz )
            if (t.s[j] == i)
            {
                XnEVbl x;
                x.vbl = &sys->vbls.s[i];
                x.val = g->p.s[j];
                if (had)  dump_cstr_OFileB (of, " && ");
                had = true;
                dump_XnEVbl (of, &x, "==");
            }
        } BLose()
    } BLose()

    dump_cstr_OFileB (of, " ->");

    t = wvbls_XnPc (pc);
    { BLoop( i, sys->vbls.sz )
        { BLoop( j, t.sz )
            if (t.s[j] == i)
            {
                XnEVbl x;
                dump_char_OFileB (of, ' ');
                x.vbl = &sys->vbls.s[i];
                x.val = g->q.s[j];
                dump_XnEVbl (of, &x, "=");
                dump_char_OFileB (of, ';');
            }
        } BLose()
    } BLose()
}


    FnWMem_do_XnSys
cons1_FnWMem_do_XnSys (const XnSys* sys)
{
    FnWMem_do_XnSys tape;
    const TableSz n = sys->vbls.sz;

    tape.sys = sys;
    tape.vals = AllocT( DomSz, n);
    tape.fixed = cons2_BitTable( n, 0 );
    InitTable( tape.evs );
    GrowTable( tape.evs, n );
    tape.evs.sz = 0;
    return tape;
}

    void
lose_FnWMem_do_XnSys (FnWMem_do_XnSys* tape)
{
    if (tape->vals)  free (tape->vals);
    lose_BitTable (&tape->fixed);
    LoseTable (tape->evs);
}

static
    void
recu_do_XnSys (BitTable* bt, const XnEVbl* a, uint n, XnSz step, XnSz bel)
{
    XnSz stepsz, bigstepsz;
    if (n == 0)
    {
        for (; step < bel; ++ step)
            set1_BitTable (*bt, step);
        return;
    }

    stepsz = a[0].vbl->stepsz;
    bigstepsz = stepsz * (1 + a[0].vbl->max);
    step += stepsz * a[0].val;

    for (; step < bel; step += bigstepsz)
        recu_do_XnSys (bt, a+1, n-1, step, step + stepsz);
}

    void
do_XnSys (FnWMem_do_XnSys* tape, BitTable bt)
{
    tape->evs.sz = 0;
    { BLoop( i, tape->fixed.sz )
        XnEVbl e;
        if (test_BitTable (tape->fixed, i))
        {
            e.val = tape->vals[i];
            e.vbl = &tape->sys->vbls.s[i];
            PushTable( tape->evs, e );
        }
    } BLose()

    recu_do_XnSys (&bt, tape->evs.s, tape->evs.sz, 0, bt.sz);
}

static
    void
recu_do_push_XnSys (TableT(XnSz)* t, const XnEVbl* a, uint n, XnSz step, XnSz bel)
{
    XnSz stepsz, bigstepsz;
    if (n == 0)
    {
        for (; step < bel; ++ step)
            PushTable( *t, step );
        return;
    }

    stepsz = a[0].vbl->stepsz;
    bigstepsz = stepsz * (1 + a[0].vbl->max);
    step += stepsz * a[0].val;

    for (; step < bel; step += bigstepsz)
        recu_do_push_XnSys (t, a+1, n-1, step, step + stepsz);
}

    void
do_push_XnSys (FnWMem_do_XnSys* tape, TableT(XnSz)* t)
{
    tape->evs.sz = 0;
    { BLoop( i, tape->fixed.sz )
        XnEVbl e;
        if (test_BitTable (tape->fixed, i))
        {
            e.val = tape->vals[i];
            e.vbl = &tape->sys->vbls.s[i];
            PushTable( tape->evs, e );
        }
    } BLose()

    recu_do_push_XnSys (t, tape->evs.s, tape->evs.sz, 0, tape->sys->legit.sz);
}

    FnWMem_detect_livelock
cons1_FnWMem_detect_livelock (const BitTable* legit)
{
    FnWMem_detect_livelock tape;

    tape.legit = legit;

    tape.cycle = cons1_BitTable (legit->sz);
    tape.tested = cons1_BitTable (legit->sz);
    InitTable( tape.testing );
    return tape;
}

    void
lose_FnWMem_detect_livelock (FnWMem_detect_livelock* tape)
{
    lose_BitTable (&tape->cycle);
    lose_BitTable (&tape->tested);
    LoseTable( tape->testing );
}

    bool
detect_livelock (FnWMem_detect_livelock* tape,
                 const TableT(Xns) xns)
{
    ujint testidx = 0;
    BitTable cycle = tape->cycle;
    BitTable tested = tape->tested;
    TableT(XnSz2) testing = tape->testing;

    if (xns.sz == 0)  return false;
    testing.sz = 0;

    op_BitTable (cycle, *tape->legit, BitTable_IDEN);
    op_BitTable (tested, *tape->legit, BitTable_IDEN);

    while (true)
    {
        XnSz i, j;
        XnSz2* top;

        if (testing.sz > 0)
        {
            top = TopTable( testing );
            i = top->i;
            j = top->j;
        }
        else
        {
            while (testidx < xns.sz &&
                   test_BitTable (tested, testidx))
            {
                ++ testidx;
            }

            if (testidx == xns.sz)  break;

            top = Grow1Table( testing );
            top->i = i = testidx;
            top->j = j = 0;
            ++ testidx;

            set1_BitTable (cycle, i);
        }

        while (j < xns.s[i].sz)
        {
            ujint k = xns.s[i].s[j];

            ++j;

            if (!test_BitTable (tested, k))
            {
                if (set1_BitTable (cycle, k))
                {
                    tape->testing = testing;
                    return true;
                }

                top->i = i;
                top->j = j;
                top = Grow1Table( testing );
                top->i = i = k;
                top->j = j = 0;
            }
        }

        if (j == xns.s[i].sz)
        {
            set1_BitTable (tested, i);
            -- testing.sz;
        }
    }
    tape->testing = testing;
    return false;
}

    FnWMem_detect_convergence
cons1_FnWMem_detect_convergence (const BitTable* legit)
{
    XnSz n = legit->sz;
    FnWMem_detect_convergence tape;

    tape.legit = legit;

    InitTable( tape.bxns );
    EnsizeTable( tape.bxns, n );
    { BLoopT( XnSz, i, n )
        InitTable( tape.bxns.s[i] );
    } BLose()

    InitTable( tape.reach );
    tape.tested = cons1_BitTable (n);
    return tape;
}

    void
lose_FnWMem_detect_convergence (FnWMem_detect_convergence* tape)
{
    { BLoopT( XnSz, i, tape->bxns.sz )
        LoseTable( tape->bxns.s[i] );
    } BLose()
    LoseTable( tape->bxns );

    LoseTable( tape->reach );
    lose_BitTable (&tape->tested);
}

    /**
     * Check to see that, for any state, there exists a path to a legit state.
     * Assume the set of legit states is closed under all transitions.
     **/
    bool
detect_convergence (FnWMem_detect_convergence* tape,
                    const TableT(Xns) xns)
{
    TableT(Xns) bxns = tape->bxns;
    TableT(XnSz) reach = tape->reach;
    BitTable tested = tape->tested;
    XnSz nreached = 0;

    { BLoopT( XnSz, i, bxns.sz )
        bxns.s[i].sz = 0;
    } BLose()
    reach.sz = 0;

    op_BitTable (tested, *tape->legit, BitTable_IDEN);

    { BLoopT( XnSz, i, xns.sz )
        if (test_BitTable (tested, i))
        {
            ++ nreached;
            PushTable( reach, i );
        }

        { BLoopT( XnSz, j, xns.s[i].sz )
            PushTable( bxns.s[xns.s[i].s[j]], i );
        } BLose()
    } BLose()

    while (reach.sz > 0)
    {
        XnSz i = *TopTable( reach );
        -- reach.sz;
        { BLoopT( XnSz, j, bxns.s[i].sz )
            XnSz k = bxns.s[i].s[j];
            if (!set1_BitTable (tested, k))
            {
                ++ nreached;
                PushTable( reach, k );
            }
        } BLose()
    }

    tape->bxns = bxns;
    tape->reach = reach;
    return (nreached == tested.sz);
}

    /** Check for livelock and deadlock freedom
     * along with fulfillment of the original protocol.
     *
     * It is assumed that all transitions in legit states are found in the
     * original protocol (we just check edge counts).
     **/
    Trit
detect_strong_convergence (FnWMem_synsearch* tape)
{
    if (detect_livelock (&tape->livelock_tape, tape->xns))  return Nil;

    { BLoopT( XnSz, i, tape->xns.sz )
        if (tape->xns.s[i].sz == 0)
            if (!test_BitTable (tape->sys->legit, i))
                return May;
    } BLose()

    { BLoopT( XnSz, i, tape->legit_states.sz )
        XnSz s0 = tape->legit_states.s[i];
        if (tape->xns.s[s0].sz != tape->legit_xns.s[i].sz)
            return May;
    } BLose()

    return Yes;
}

    void
back1_Xn (TableT(Xns)* xns, TableT(XnSz)* stk)
{
    ujint n = *TopTable(*stk);
    ujint off = stk->sz - (n + 1);

    { BLoopT( ujint, i, n )
        xns->s[stk->s[off + i]].sz -= 1;
    } BLose()

    stk->sz = off;
}

    FnWMem_synsearch
cons1_FnWMem_synsearch (const XnSys* sys)
{
    FnWMem_synsearch tape;

    tape.stabilizing = false;
    tape.sys = sys;
    tape.livelock_tape = cons1_FnWMem_detect_livelock (&sys->legit);
    tape.convergence_tape = cons1_FnWMem_detect_convergence (&sys->legit);
    tape.dostates_tape = cons1_FnWMem_do_XnSys (sys);

    InitTable( tape.xns );
    GrowTable( tape.xns, sys->legit.sz );
    { BLoopT( XnSz, i, tape.xns.sz )
        InitTable( tape.xns.s[i] );
    } BLose()

    InitTable( tape.xn_stk );
    InitTable( tape.rules );
    InitTable( tape.may_rules );
    InitTable( tape.cmp_xn_stk );
    tape.n_cached_rules = 0;
    tape.n_cached_may_rules = 0;
    tape.rule_nwvbls = 0;
    tape.rule_nrvbls = 0;
    { BLoop( i, sys->pcs.sz )
        uint nwvbls = sys->pcs.s[i].nwvbls;
        uint nrvbls = sys->pcs.s[i].nrvbls;
        if (nwvbls > tape.rule_nwvbls)  tape.rule_nwvbls = nwvbls;
        if (nrvbls > tape.rule_nrvbls)  tape.rule_nrvbls = nrvbls;
    } BLose()

    InitTable( tape.legit_states );
    { BLoopT( XnSz, i, sys->legit.sz )
        if (test_BitTable (sys->legit, i))
            PushTable( tape.legit_states, i );
    } BLose()

    { BLoopT( XnSz, i, sys->legit_rules.sz )
        add_XnRule (&tape, &sys->legit_rules.s[i]);
    } BLose()

    InitTable( tape.legit_xns );
    EnsizeTable( tape.legit_xns, tape.legit_states.sz );
    { BLoopT( XnSz, i, tape.legit_states.sz )
        InitTable( tape.legit_xns.s[i] );
        CopyTable( tape.legit_xns.s[i], tape.xns.s[tape.legit_states.s[i]] );
    } BLose()

    { BLoopT( XnSz, i, sys->legit_rules.sz )
        back1_Xn (&tape.xns, &tape.xn_stk);
    } BLose()

    return tape;
}

    void
lose_FnWMem_synsearch (FnWMem_synsearch* tape)
{
    lose_FnWMem_detect_livelock (&tape->livelock_tape);
    lose_FnWMem_detect_convergence (&tape->convergence_tape);
    lose_FnWMem_do_XnSys (&tape->dostates_tape);

    { BLoopT( XnSz, i, tape->xns.sz )
        LoseTable( tape->xns.s[i] );
    } BLose()
    LoseTable( tape->xns );
    LoseTable( tape->xn_stk );

    { BLoop( i, tape->n_cached_rules )
        LoseTable( tape->rules.s[i].p );
        LoseTable( tape->rules.s[i].q );
    } BLose()
    LoseTable( tape->rules );

    { BLoopT( XnSz, i, tape->n_cached_may_rules )
        LoseTable( tape->may_rules.s[i] );
    } BLose()
    LoseTable( tape->may_rules );

    LoseTable( tape->cmp_xn_stk );

    LoseTable( tape->legit_states );

    { BLoopT( XnSz, i, tape->legit_xns.sz )
        LoseTable( tape->legit_xns.s[i] );
    } BLose()
    LoseTable( tape->legit_xns );
}

#define DelTo( a, b, c ) \
    ((b) > (c) ? (a) - ((b) - (c)) : (a) + ((c) - (b)))

    XnSz
apply1_XnRule (const XnRule* g, const XnSys* sys, XnSz sidx)
{
    const XnPc* pc = &sys->pcs.s[g->pc];
    { BLoop( i, g->q.sz )
        XnSz stepsz = sys->vbls.s[pc->vbls.s[i]].stepsz;
        XnSz a = stepsz * g->p.s[i];
        XnSz b = stepsz * g->q.s[i];
        sidx = DelTo( sidx, a, b );
    } BLose()
    return sidx;
}

    void
add_XnRule (FnWMem_synsearch* tape, const XnRule* g)
{
    TableT(Xns)* xns = &tape->xns;
    TableT(XnSz)* stk = &tape->xn_stk;
    XnSz nadds = 0;
    XnSz sa, sb;
    DeclTable( XnSz, t );
    FnWMem_do_XnSys* fix = &tape->dostates_tape;

    nadds = stk->sz;

    { BLoop( i, g->p.sz )
        const XnPc* pc = &tape->sys->pcs.s[g->pc];
        uint vi = pc->vbls.s[i];
        fix->vals[vi] = g->p.s[i];
        set1_BitTable (fix->fixed, vi);
    } BLose()

    do_push_XnSys (fix, stk);

    { BLoop( i, g->p.sz )
        const XnPc* pc = &tape->sys->pcs.s[g->pc];
        uint vi = pc->vbls.s[i];
        set0_BitTable (fix->fixed, vi);
    } BLose()

        /* Overlay the table.*/
    t.s = &stk->s[nadds];
    t.sz = stk->sz - nadds;
    stk->sz = nadds;
    nadds = 0;

    Claim2( t.sz ,>, 0 );
    sa = t.s[0];
    sb = apply1_XnRule (g, tape->sys, sa);

    { BLoopT( XnSz, i, t.sz )
        bool add = true;
        XnSz s0 = t.s[i];
        XnSz s1 = DelTo( s0, sa, sb );
        TableT(XnSz)* src = &xns->s[s0];

        { BLoopT( XnSz, j, src->sz )
            if (src->s[j] == s1)
            {
                add = false;
                break;
            }
        } BLose()

        if (add)
        {
            PushTable( *src, s1 );
            t.s[nadds] = s0;
            ++ stk->sz;
            ++ nadds;
        }
    } BLose()

    PushTable( *stk, nadds );
}

static
    int
cmp_XnSz (const void* pa, const void* pb)
{
    const XnSz a = *(XnSz*) pa;
    const XnSz b = *(XnSz*) pb;
    return ((a > b) ? +1 :
            (a < b) ? -1 :
            0);
}


static
    void
set_may_rules (FnWMem_synsearch* tape, TableT(XnSz)* may_rules, XnRule* g)
{
    const XnSys* restrict sys = tape->sys;

        /* Ensure protocol is closed.*/
    { BLoopT( XnSz, i, tape->legit_xns.sz )
        const TableT(XnSz)* t = &tape->legit_xns.s[i];
        { BLoopT( XnSz, j, t->sz )
            if (!test_BitTable (sys->legit, t->s[j]))
            {
                DBog0( "Protocol breaks closure." );
                may_rules->sz = 0;
                return;
            }
        } BLose()
    } BLose()

    { BLoopT( XnSz, i, sys->n_rule_steps )
            /* XnSz rule_step = i; */
        XnSz rule_step = sys->n_rule_steps - 1 - i;

        bool add = true;
        bool test_selfloop = true;
        TableT(XnSz) t;

        rule_XnSys (g, sys, rule_step);
        add_XnRule (tape, g);

        t = tape->xn_stk;
        -- t.sz;

        { BLoopT( XnSz, j, t.sz )
            const XnSz s0 = t.s[j];

                /* Do not add rules which cause
                 * bad transitions from legit states.
                 */
            if (test_BitTable (sys->legit, s0))
            {
                const XnSz s1 = tape->xns.s[s0].s[0];
                const XnSz* elt;
                XnSz legit_idx;

                test_selfloop = false;

                elt = bsearch (&s0, tape->legit_states.s,
                               tape->legit_states.sz, sizeof(XnSz),
                               cmp_XnSz);

                legit_idx = IdxEltTable( tape->legit_states, elt );

                elt = bsearch (&s1,
                               tape->legit_xns.s[legit_idx].s,
                               tape->legit_xns.s[legit_idx].sz,
                               sizeof(XnSz),
                               cmp_XnSz);

                if (!elt)
                {
                    add = false;
                    break;
                }
            }
        } BLose()

        if (add && test_selfloop)
        {
            const XnSz s0 = t.s[0];
            add = (s0 != tape->xns.s[s0].s[0]);
        }

        back1_Xn (&tape->xns, &tape->xn_stk);

        if (add)
            PushTable( *may_rules, rule_step );
    } BLose()
}

static
    XnRule*
grow1_rules_synsearch (FnWMem_synsearch* tape)
{
    XnRule* g = Grow1Table( tape->rules );
    if (tape->rules.sz > tape->n_cached_rules)
    {
        *g = cons2_XnRule (tape->rule_nrvbls,
                           tape->rule_nwvbls);
        ++ tape->n_cached_rules;
    }
    return g;
}

static
    TableT(XnSz)*
grow1_may_rules_synsearch (FnWMem_synsearch* tape)
{
    TableT(XnSz)* may_rules = Grow1Table( tape->may_rules );

    if (tape->may_rules.sz > tape->n_cached_may_rules)
    {
        InitTable( *may_rules );
        ++ tape->n_cached_may_rules;
    }

    return may_rules;
}

    void
synsearch (FnWMem_synsearch* tape)
{
    const XnSys* restrict sys = tape->sys;
    XnRule* g;
    XnSz nreqrules = 0;
    TableT(XnSz)* may_rules;

    g = grow1_rules_synsearch (tape);
    may_rules = grow1_may_rules_synsearch (tape);

    may_rules->sz = 0;

    if (tape->rules.sz == 1)
    {
        if (all_BitTable (sys->legit))
        {
            tape->stabilizing = true;
            CopyTable( tape->rules, sys->legit_rules );
            return;
        }
        set_may_rules (tape, may_rules, g);
    }
    else
    {
        CopyTable( *may_rules, *(may_rules - 1) );
    }

        /* Trim down the next possible steps.*/
    {
        XnSz off = 0;
        { BLoopT( XnSz, i, may_rules->sz )
            Trit stabilizing;
            XnSz rule_step = may_rules->s[i];

            rule_XnSys (g, sys, rule_step);
            add_XnRule (tape, g);

            stabilizing = detect_strong_convergence (tape);

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
                bool add = false;
                DeclTable( XnSz, t );
                t.sz = *TopTable( tape->xn_stk );
                t.s = &tape->xn_stk.s[tape->xn_stk.sz - 1 - t.sz];

                Claim2( t.sz ,>, 0 );

                { BLoopT( XnSz, j, t.sz )
                    XnSz s0 = t.s[j];
                        /* Resolves a deadlock or
                         * helps fulfill the original protocol.
                         */
                    if (tape->xns.s[s0].sz == 1 ||
                        test_BitTable (sys->legit, s0))
                    {
                        add = true;
                        break;
                    }
                } BLose()

                if (!add)
                {
                    stabilizing = Nil;
                }
            }

            back1_Xn (&tape->xns, &tape->xn_stk);

            if (stabilizing == May)
            {
                may_rules->s[off] = may_rules->s[i];
                ++ off;
            }
        } BLose()
        may_rules->sz = off;
    }

        /* Check that a weakly stabilizing protocol
         * exists with the rules we have left.
         */
    {
        bool weak = true;
        { BLoopT( XnSz, i, may_rules->sz )
            XnSz rule_step = may_rules->s[i];
            rule_XnSys (g, sys, rule_step);
            add_XnRule (tape, g);
        } BLose()

        weak = detect_convergence (&tape->convergence_tape, tape->xns);

        { BLoopT( XnSz, i, tape->legit_states.sz )
            XnSz nout = tape->xns.s[tape->legit_states.s[i]].sz;
            if (nout != tape->legit_xns.s[i].sz)
                weak = false;
        } BLose()

        if (weak)
        {
            XnSz idx = tape->xn_stk.sz;
            tape->cmp_xn_stk.sz = 0;

            { BLoopT( XnSz, i, may_rules->sz )
                const XnSz n = tape->xn_stk.s[idx - 1];
                idx -= n + 1;
                { BLoopT( XnSz, j, n + 1 )
                    PushTable( tape->cmp_xn_stk, tape->xn_stk.s[idx+j] );
                } BLose()
            } BLose()
        }

        { BLoopT( XnSz, i, may_rules->sz )
            back1_Xn (&tape->xns, &tape->xn_stk);
        } BLose()

        if (!weak)
        {
            may_rules->sz = 0;
        }
    }

        /* Find rules which are necessary.*/
    if (true)
    {
        XnSz off = 0;
        XnSz stk_idx, cmp_stk_idx;

            /* Add all rules backwards, to find which are absolutely required.*/
        { BLoopT( XnSz, i, may_rules->sz )
            XnSz rule_step = may_rules->s[may_rules->sz - 1 - i];
            rule_XnSys (g, sys, rule_step);
            add_XnRule (tape, g);
        } BLose()

        stk_idx = tape->xn_stk.sz;
        cmp_stk_idx = tape->cmp_xn_stk.sz;

        { BLoopT( XnSz, i, may_rules->sz )
            bool required = false;
            const XnSz nas = tape->xn_stk.s[stk_idx-1];
            const XnSz nbs = tape->cmp_xn_stk.s[cmp_stk_idx-1];
            const XnSz* as;
            const XnSz* bs;

            stk_idx -= nas + 1;
            cmp_stk_idx -= nbs + 1;

            as = &tape->xn_stk.s[stk_idx];
            bs = &tape->cmp_xn_stk.s[cmp_stk_idx];

            { BLoopT( XnSz, j, nas )
                const XnSz s0 = as[j];
                { BLoopT( XnSz, k, nbs )
                    if (s0 == bs[k] &&
                        (tape->xns.s[s0].sz == 1 ||
                         test_BitTable (sys->legit, s0)))
                    {
                        required = true;
                        j = nas;
                        k = nbs;
                    }
                } BLose()
            } BLose()

            tape->cmp_xn_stk.sz -= nbs + 1;

            if (required)
            {
                rule_XnSys (g, sys, may_rules->s[i]);
                g = grow1_rules_synsearch (tape);
                ++ nreqrules;
            }
            else
            {
                may_rules->s[off] = may_rules->s[i];
                ++ off;
            }
        } BLose()

        { BLoopT( XnSz, i, may_rules->sz )
            back1_Xn (&tape->xns, &tape->xn_stk);
        } BLose()

        may_rules->sz = off;
        Claim2( tape->cmp_xn_stk.sz ,==, 0 );
    }

    if (nreqrules > 0)
    {
        Trit stabilizing = May;
        -- tape->rules.sz;
        g = g - nreqrules;
#if 0
        DBog3( "Assert %u/%u rules at depth %u.",
               nreqrules,
               may_rules->sz + nreqrules,
               tape->may_rules.sz-1 );
#endif
        { BLoop( i, nreqrules )
            add_XnRule (tape, g + i);
        } BLose()

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
            synsearch (tape);
            if (tape->stabilizing)  return;
        }

        { BLoop( i, nreqrules )
            back1_Xn (&tape->xns, &tape->xn_stk);
        } BLose()
    }
    else  while (may_rules->sz > 0)
    {
        XnSz rule_step = *TopTable( *may_rules );
        -- may_rules->sz;
        rule_XnSys (g, sys, rule_step);

        add_XnRule (tape, g);
        if (tape->may_rules.sz-1 < 40 && false)
                /* if (tape->may_rules.sz-1 >= 0 || false) */
        {
            OFileB* of = stderr_OFileB ();
            dump_cstr_OFileB (of, " -- ");
            dump_uint_OFileB (of, tape->may_rules.sz - 1);
            dump_cstr_OFileB (of, " -- ");
            dump_promela_XnRule (of, g, sys);
            dump_char_OFileB (of, '\n');
            flush_OFileB (of);
        }

        synsearch (tape);
        if (tape->stabilizing)  return;
        back1_Xn (&tape->xns, &tape->xn_stk);

        g = TopTable( tape->rules );
        may_rules = TopTable( tape->may_rules );
    }

    if (nreqrules > 0)  tape->rules.sz -= nreqrules;
    else                -- tape->rules.sz;

    -- tape->may_rules.sz;
        /* if (tape->rules.sz == 58)  exit(1); */
}


    void
testfn_detect_livelock ()
{
    BitTable legit = cons2_BitTable (6, 0);
    DeclTable( Xns, xns );
    FnWMem_detect_livelock mem_detect_livelock;
    bool livelock_exists;

    GrowTable( xns, legit.sz );
    { BLoop( i, xns.sz )
        InitTable( xns.s[i] );
    } BLose()

    mem_detect_livelock = cons1_FnWMem_detect_livelock (&legit);


    PushTable( xns.s[0], 1 );
    livelock_exists = detect_livelock (&mem_detect_livelock, xns);
    Claim( !livelock_exists );

    PushTable( xns.s[1], 5 );
    PushTable( xns.s[1], 3 );
    PushTable( xns.s[2], 1 );
    PushTable( xns.s[3], 4 );
    PushTable( xns.s[4], 2 );

    livelock_exists = detect_livelock (&mem_detect_livelock, xns);
    Claim( livelock_exists );

    lose_FnWMem_detect_livelock (&mem_detect_livelock);

    { BLoop( i, xns.sz )
        LoseTable( xns.s[i] );
    } BLose()
    LoseTable( xns );
    lose_BitTable (&legit);
}

static
    void
sat3_legit_XnSys (FnWMem_do_XnSys* fix,
                  BitTable bt,
                  XnSys* sys, TableT(Disj3) cnf,
                  const uint npcs,
                  const uint* x_idcs,
                  const uint* y_idcs)
{
    bool ring = (npcs != 3);
#if 0
    OFileB* of = stderr_OFileB ();
    dump_BitTable (of, sys->legit);
    dump_char_OFileB (of, '\n');
#endif

#if 1
        /* Enforce identity.*/
    { BLoop( lo, npcs )
        const uint nsatvbls = 1 + (uint) sys->vbls.s[x_idcs[0]].max;

        { BLoop( offset, 2 )
            const uint hi = (lo+1+offset) % npcs;

            wipe_BitTable (bt, 0);

            set1_BitTable (fix->fixed, x_idcs[lo]);
            set1_BitTable (fix->fixed, x_idcs[hi]);

            { BLoop( val, nsatvbls )
                fix->vals[x_idcs[lo]] = val;
                fix->vals[x_idcs[hi]] = val;
                do_XnSys (fix, bt);
            } BLose()

            set0_BitTable (fix->fixed, x_idcs[lo]);
            set0_BitTable (fix->fixed, x_idcs[hi]);

            op_BitTable (bt, bt, BitTable_NOT);

            set1_BitTable (fix->fixed, y_idcs[lo]);
            set1_BitTable (fix->fixed, y_idcs[hi]);
            { BLoop( val, 2 )
                fix->vals[y_idcs[lo]] = val;
                fix->vals[y_idcs[hi]] = val;
                do_XnSys (fix, bt);
            } BLose()
            set0_BitTable (fix->fixed, y_idcs[lo]);
            set0_BitTable (fix->fixed, y_idcs[hi]);

            op_BitTable (sys->legit, bt, BitTable_AND);
        } BLose()
    } BLose()
#endif

        /* Clauses.*/
    { BLoop( ci, cnf.sz )
        static const byte perms[][3] = {
            { 0, 1, 2 },
            { 0, 2, 1 },
            { 1, 0, 2 },
            { 1, 2, 0 },
            { 2, 0, 1 },
            { 2, 1, 0 }
        };
            /* Only use permutations for the ring.*/
        const uint nperms = (ring ? ArraySz( perms ) : 1);
            /* Only slide the window for the ring.*/
        const uint nwindows = (ring ? npcs : 1);

        { BLoop( permi, nperms )
            Disj3 clause;

            { BLoop( i, 3 )
                clause.terms[i] = cnf.s[ci].terms[ perms[permi][i] ];
            } BLose()

            { BLoop( lo, nwindows )

                wipe_BitTable (bt, 0);

                    /* Get variables on the stack.*/
                { BLoop( i, 3 )
                    int v = clause.terms[i];
                    const uint pcidx = x_idcs[(lo + i) % npcs];

                    set1_BitTable (fix->fixed, pcidx);
                    fix->vals[pcidx] = (DomSz) (v > 0 ? v : -v) - 1;
                } BLose()

                do_XnSys (fix, bt);
                op_BitTable (bt, bt, BitTable_NOT);

                { BLoop( i, 3 )
                    int v = clause.terms[i];
                    const uint pcidx = y_idcs[(lo + i) % npcs];

                    set1_BitTable (fix->fixed, pcidx);
                    fix->vals[pcidx] = (v > 0);
                    do_XnSys (fix, bt);
                    set0_BitTable (fix->fixed, pcidx);
                } BLose()

                op_BitTable (sys->legit, bt, BitTable_AND);

                wipe_BitTable (fix->fixed, 0);
            } BLose()
        } BLose()
    } BLose()


#if 0
    dump_BitTable (of, sys->legit);
    dump_char_OFileB (of, '\n');

    if (false)
    { BLoopT( XnSz, i, sys->legit.sz )
        if (test_BitTable (sys->legit, i))
        {
            dump_char_OFileB (of, '+');
            dump_promela_state_XnSys (of, sys, i);
            dump_char_OFileB (of, '\n');
        }
        else
        {
            dump_char_OFileB (of, '-');
            dump_promela_state_XnSys (of, sys, i);
            dump_char_OFileB (of, '\n');
        }
    } BLose()

    flush_OFileB (of);
#endif
}



    XnSys
sat3_XnSys ()
{
    Disj3 clauses[] = {
            /* {{ 1, 3, 1 }}, */
        {{ -2, 1, -2 }},
        {{ -2, -2, -2 }},
            /* {{ 2, -1, 2 }}, */
        {{ 1, 1, 1 }}
    };
    DeclTable( Disj3, cnf );
    const uint nsatvbls = 2;
    uint x_idcs[3];
    uint y_idcs[3];
    uint sat_idx;
    DecloStack( XnSys, sys );
    OFileB name = dflt_OFileB ();

    *sys = dflt_XnSys ();
    cnf.s = clauses;
    cnf.sz = ArraySz( clauses );

    { BLoop( r, 3 )
        PushTable( sys->pcs, dflt_XnPc () );

        x_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, dflt_XnVbl () );
        y_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, dflt_XnVbl () );
    } BLose()

    PushTable( sys->pcs, dflt_XnPc () );
    sat_idx = sys->vbls.sz;
    PushTable( sys->vbls, dflt_XnVbl () );

    { BLoop( r, 3 )
        XnVbl* x = &sys->vbls.s[x_idcs[r]];
        XnVbl* y = &sys->vbls.s[y_idcs[r]];

        x->max = nsatvbls-1;
        y->max = 1;

        flush_OFileB (&name);
        printf_OFileB (&name, "x%u", r);
        CopyTable( x->name, name.buf );

        flush_OFileB (&name);
        printf_OFileB (&name, "y%u", r);
        CopyTable( y->name, name.buf );

        assoc_XnSys (sys, r, x_idcs[r], May);
        assoc_XnSys (sys, r, y_idcs[r], Yes);
        assoc_XnSys (sys, r, sat_idx, May);

        assoc_XnSys (sys, 3, x_idcs[r], May);
        assoc_XnSys (sys, 3, y_idcs[r], May);
    } BLose()

    sys->vbls.s[sat_idx].max = 1;
    flush_OFileB (&name);
    dump_cstr_OFileB (&name, "sat");
    CopyTable( sys->vbls.s[sat_idx].name, name.buf );
    assoc_XnSys (sys, 3, sat_idx, Yes);

    accept_topology_XnSys (sys);

    {
        DecloStack( FnWMem_do_XnSys, fix );
        BitTable bt = cons2_BitTable (sys->legit.sz, 0);

        *fix = cons1_FnWMem_do_XnSys (sys);

        fix->vals[sat_idx] = 1;
        set1_BitTable (fix->fixed, sat_idx);
        do_XnSys (fix, bt);
        op_BitTable (sys->legit, bt, BitTable_AND);

        sat3_legit_XnSys (fix, bt, sys, cnf, 3, x_idcs, y_idcs);

        lose_BitTable (&bt);
        lose_FnWMem_do_XnSys (fix);
    }

    /*
    { BLoop( i, sys->legit.sz )
        if (test_BitTable (sys->legit, i))
            DBog1( "%u is true", i );
    } BLose()
    */
    DBog1( "size is %u", (uint) sys->legit.sz );

    lose_OFileB (&name);
    return *sys;
}

    XnSys
sat3_ring_XnSys ()
{
    Disj3 clauses[] = {
            /* {{ 1, 3, 1 }}, */
            /* {{ -2, 1, -2 }}, */
            /* {{ -2, -2, -2 }}, */
            /* {{ 2, -1, 2 }}, */
        {{ -2, -2, -2 }},
        {{ 2, 1, 2 }},
        {{ -1, 2, -1 }}
            /* {{ 1, 1, 1 }} */
    };
    DeclTable( Disj3, cnf );
    const uint nsatvbls = 3;
    uint x_idcs[5];
    uint y_idcs[ArraySz( x_idcs )];
    uint sat_idcs[ArraySz( x_idcs )];
    const uint npcs = ArraySz( x_idcs );
    DecloStack( XnSys, sys );
    OFileB name = dflt_OFileB ();

    *sys = dflt_XnSys ();
    cnf.s = clauses;
    cnf.sz = ArraySz( clauses );

    { BLoop( r, npcs )
        PushTable( sys->pcs, dflt_XnPc () );
    } BLose()

    { BLoop( r, npcs )
        x_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, dflt_XnVbl () );
    } BLose()

    { BLoop( r, npcs )
        y_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, dflt_XnVbl () );
    } BLose()

    { BLoop( r, npcs )
        sat_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, dflt_XnVbl () );
    } BLose()

    { BLoop( r, npcs )
        XnVbl* x = &sys->vbls.s[x_idcs[r]];
        XnVbl* y = &sys->vbls.s[y_idcs[r]];
        XnVbl* sat = &sys->vbls.s[sat_idcs[r]];

        x->max = nsatvbls - 1;
        y->max = 1;
        sat->max = 1;

        flush_OFileB (&name);
        printf_OFileB (&name, "x%u", r);
        CopyTable( x->name, name.buf );

        flush_OFileB (&name);
        printf_OFileB (&name, "y%u", r);
        CopyTable( y->name, name.buf );

        flush_OFileB (&name);
        printf_OFileB (&name, "sat%u", r);
        CopyTable( sat->name, name.buf );

            /* Process r */
        assoc_XnSys (sys, r, x_idcs[r], May);
        assoc_XnSys (sys, r, y_idcs[r], Yes);
        assoc_XnSys (sys, r, sat_idcs[r], Yes);

            /* Process r+1 */
        assoc_XnSys (sys, (r + 1) % npcs, x_idcs[r], May);
        assoc_XnSys (sys, (r + 1) % npcs, y_idcs[r], May);
        assoc_XnSys (sys, (r + 1) % npcs, sat_idcs[r], May);

            /* Process r-1 */
        assoc_XnSys (sys, (r + npcs - 1) % npcs, x_idcs[r], May);
        assoc_XnSys (sys, (r + npcs - 1) % npcs, y_idcs[r], May);
        assoc_XnSys (sys, (r + npcs - 1) % npcs, sat_idcs[r], May);
    } BLose()

    lose_OFileB (&name);

    accept_topology_XnSys (sys);

    {
        DecloStack( FnWMem_do_XnSys, fix );
        BitTable bt = cons2_BitTable (sys->legit.sz, 0);

        *fix = cons1_FnWMem_do_XnSys (sys);

        { BLoop( i, npcs )
            fix->vals[sat_idcs[i]] = 1;
            set1_BitTable (fix->fixed, sat_idcs[i]);
        } BLose()

        do_XnSys (fix, bt);
        op_BitTable (sys->legit, bt, BitTable_AND);

        sat3_legit_XnSys (fix, bt, sys, cnf, npcs, x_idcs, y_idcs);

        lose_BitTable (&bt);
        lose_FnWMem_do_XnSys (fix);
    }

    return *sys;
}

    void
dump_promela_select (OFileB* of, const XnVbl* vbl)
{
    XnEVbl x;
    x.vbl = vbl;
    dump_cstr_OFileB (of, "if\n");
    { BLoop( i, (uint) (vbl->max+1) )
        x.val = i;
        dump_cstr_OFileB (of, ":: true -> ");
        dump_XnEVbl (of, &x, "=");
        dump_cstr_OFileB (of, ";\n");
    } BLose()

    dump_cstr_OFileB (of, "fi;\n");
}

    void
dump_promela_pc (OFileB* of, const XnPc* pc, const XnSys* sys,
                 const TableT(XnRule) rules)
{
    const uint pcidx = IdxEltTable (sys->pcs, pc);
    dump_cstr_OFileB (of, "proctype P");
    dump_uint_OFileB (of, pcidx);
    dump_cstr_OFileB (of, " ()\n{\n");
    dump_cstr_OFileB (of, "do\n");
    dump_cstr_OFileB (of, ":: true ->\n");
    dump_cstr_OFileB (of, "atomic { setlegit (); };\n");
    dump_cstr_OFileB (of, "if\n");
    { BLoop( i, rules.sz )
        const XnRule* g = &rules.s[i];
        if (g->pc == pcidx)
        {
            dump_cstr_OFileB (of, ":: atomic {");
            dump_promela_XnRule (of, g, sys);
            dump_cstr_OFileB (of, "};\n");
        }
    } BLose()
    dump_cstr_OFileB (of, "fi;\n");
    dump_cstr_OFileB (of, "od;\n");
    dump_cstr_OFileB (of, "}\n\n");
    
}

    void
dump_promela (OFileB* of, const XnSys* sys, const TableT(XnRule) rules)
{
    dump_cstr_OFileB (of, "bool Legit = false;\n");
    { BLoop( i, sys->vbls.sz )
        const XnVbl* x = &sys->vbls.s[i];
        if (x->max <= 1)
            dump_cstr_OFileB (of, "bit");
        else
            dump_cstr_OFileB (of, "byte");

        dump_char_OFileB (of, ' ');
        dump_cstr_OFileB (of, x->name.s );
        dump_cstr_OFileB (of, ";\n");
    } BLose()

    dump_cstr_OFileB (of, "inline setlegit ()\n");
    dump_cstr_OFileB (of, "{\n");
    dump_cstr_OFileB (of, "if\n");
    { BLoopT( XnSz, i, sys->legit.sz )
        if (test_BitTable (sys->legit, i))
        {
            dump_cstr_OFileB (of, ":: ");
            dump_promela_state_XnSys (of, sys, i);
            dump_cstr_OFileB (of, " -> Legit = true;\n");
        }
    } BLose()
    dump_cstr_OFileB (of, ":: else -> Legit = false;\n");
    dump_cstr_OFileB (of, "fi;\n");
    dump_cstr_OFileB (of, "}\n");

    { BLoop( i, sys->pcs.sz )
        dump_promela_pc (of, &sys->pcs.s[i], sys, rules);
    } BLose()

    dump_cstr_OFileB (of, "init {\n");

    { BLoop( i, sys->vbls.sz )
        const XnVbl* x = &sys->vbls.s[i];
        dump_promela_select (of, x);
    } BLose()

    { BLoop( i, sys->pcs.sz )
        dump_cstr_OFileB (of, "run P");
        dump_uint_OFileB (of, i);
        dump_cstr_OFileB (of, " ();\n");
    } BLose()

    dump_cstr_OFileB (of, "}\n");

    dump_cstr_OFileB (of, "ltl {\n");
    dump_cstr_OFileB (of, "<> Legit && [] (Legit -> [] Legit)\n");

    dump_cstr_OFileB (of, "}\n");
}

    int
main ()
{
    DecloStack( XnSys, sys );
    init_sys_cx ();
#if 1
    *sys = sat3_XnSys ();
#else
    *sys = sat3_ring_XnSys ();
#endif

    testfn_detect_livelock ();

    {
        FnWMem_synsearch tape = cons1_FnWMem_synsearch (sys);
        synsearch (&tape);
        if (tape.stabilizing)
        {
            FileB pmlf;
            DBog0( "Solution found! :)" );
#if 0
            { BLoopT( XnSz, i, tape.rules.sz )
                dump_promela_XnRule (stderr_OFileB (), &tape.rules.s[i], sys);
                dump_char_OFileB (stderr_OFileB (), '\n');
            } BLose()
#endif

            init_FileB (&pmlf);
            seto_FileB (&pmlf, true);
            open_FileB (&pmlf, 0, "model.pml");
            dump_promela (&pmlf.xo, sys, tape.rules);
            lose_FileB (&pmlf);
        }
        else
        {
            DBog0( "No solution. :(" );
        }
        lose_FnWMem_synsearch (&tape);
    }

    lose_XnSys (sys);
    lose_sys_cx ();
    return 0;
}

