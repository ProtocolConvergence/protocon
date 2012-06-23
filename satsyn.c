
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
};

struct XnVbl
{
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
};

struct FnWMem_detect_livelock
{
    BitTable cycle;
    BitTable tested;
    TableT(XnSz2) testing;
    const BitTable* legit;
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
    FnWMem_do_XnSys dostates_tape;
    TableT(Xns) xns;
    TableT(XnSz) xn_stk;
    TableT(XnRule) rules;
    uint cached_nrules;
    uint rule_nwvbls;
    uint rule_nrvbls;
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
    return pc;
}

    void
lose_XnPc (XnPc* pc)
{
    LoseTable( pc->vbls );
}

    XnVbl
dflt_XnVbl ()
{
    XnVbl x;
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
    LoseTable( x->pcs );
}

    XnSys
dflt_XnSys ()
{
    XnSys sys;
    InitTable( sys.pcs );
    InitTable( sys.vbls );
    sys.legit = dflt_BitTable ();
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
}


    void
dump_state_XnSys (OFileB* of, const XnSys* sys, XnSz sidx)
{
    { BLoop( i, sys->vbls.sz )
        const XnVbl* x = &sys->vbls.s[i];
        uint v = sidx / x->stepsz;
        sidx = sidx % x->stepsz;
        dump_uint_OFileB (of, v);
        dump_char_OFileB (of, ' ');
    } BLose()
}

    void
dump_XnRule (OFileB* of, const XnRule* g, const XnSys* sys)
{
    XnPc* pc = &sys->pcs.s[g->pc];
    TableT(XnSz) t;
    dump_char_OFileB (of, '(');
    dump_char_OFileB (of, 'P');
    dump_uint_OFileB (of, g->pc);
    dump_char_OFileB (of, ':');

    t = rvbls_XnPc (pc);
    { BLoop( i, sys->vbls.sz )
        { BLoop( j, t.sz )
            if (t.s[j] == i)
            {
                dump_cstr_OFileB (of, " x");
                dump_uint_OFileB (of, i);
                dump_char_OFileB (of, '=');
                dump_uint_OFileB (of, g->p.s[j]);
            }
        } BLose()
    } BLose()

    dump_cstr_OFileB (of, " ->");

    t = wvbls_XnPc (pc);
    { BLoop( i, sys->vbls.sz )
        { BLoop( j, t.sz )
            if (t.s[j] == i)
            {
                dump_cstr_OFileB (of, " x");
                dump_uint_OFileB (of, i);
                dump_char_OFileB (of, '=');
                dump_uint_OFileB (of, g->q.s[j]);
            }
        } BLose()
    } BLose()
    dump_char_OFileB (of, ')');
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

    void
sat3_legit_XnSys (XnSys* sys, TableT(Disj3) cnf)
{
    BitTable bt = cons2_BitTable (sys->legit.sz, 0);
    OFileB* of = stderr_OFileB ();
    FnWMem_do_XnSys fix = cons1_FnWMem_do_XnSys (sys);

    {
        const uint satidx = 6;
        fix.vals[satidx] = 1;
        set1_BitTable (fix.fixed, satidx);
        do_XnSys (&fix, bt);
        op_BitTable (sys->legit, bt, BitTable_AND);
    }

    dump_BitTable (of, sys->legit);
    dump_char_OFileB (of, '\n');



#if 1
    { BLoop( i, 3 )
        const uint n = 1 + (uint) sys->vbls.s[0].max;
        uint j;
        for (j = i+1; j < 3; ++j)
        {
            wipe_BitTable (bt, 0);

            set1_BitTable (fix.fixed, 2*i);
            set1_BitTable (fix.fixed, 2*j);

            { BLoop( val, n )
                fix.vals[2*i] = val;
                fix.vals[2*j] = val;
                do_XnSys (&fix, bt);
            } BLose()

            set0_BitTable (fix.fixed, 2*i);
            set0_BitTable (fix.fixed, 2*j);

            op_BitTable (bt, bt, BitTable_NOT);

            set1_BitTable (fix.fixed, 2*i+1);
            set1_BitTable (fix.fixed, 2*j+1);
            { BLoop( val, 2 )
                fix.vals[2*i+1] = val;
                fix.vals[2*j+1] = val;
                do_XnSys (&fix, bt);
            } BLose()
            set0_BitTable (fix.fixed, 2*i+1);
            set0_BitTable (fix.fixed, 2*j+1);

            op_BitTable (sys->legit, bt, BitTable_AND);
        }
    } BLose()
#endif

        /* Clauses.*/
    { BLoop( ci, cnf.sz )
        static const byte perms[][3] = {
#if 1
            { 0, 1, 2 }
#else
            { 0, 1, 2 },
            { 0, 2, 1 },
            { 1, 0, 2 },
            { 1, 2, 0 },
            { 2, 0, 1 },
            { 2, 1, 0 }
#endif
        };

        { BLoop( permi, ArraySz( perms ) )
            Disj3 clause;

            { BLoop( i, 3 )
                clause.terms[i] = cnf.s[ci].terms[ perms[permi][i] ];
            } BLose()

            wipe_BitTable (bt, 0);

                /* Get variables on the stack.*/
            { BLoop( i, 3 )
                int v = clause.terms[i];

                set1_BitTable (fix.fixed, 2*i);
                fix.vals[2*i] = (DomSz) (v > 0 ? v : -v) - 1;
            } BLose()

            do_XnSys (&fix, bt);
            op_BitTable (bt, bt, BitTable_NOT);

            { BLoop( i, 3 )
                int v = clause.terms[i];

                set1_BitTable (fix.fixed, 2*i+1);
                fix.vals[2*i+1] = (v > 0);
                do_XnSys (&fix, bt);
                set0_BitTable (fix.fixed, 2*i+1);
            } BLose()

            op_BitTable (sys->legit, bt, BitTable_AND);

            wipe_BitTable (fix.fixed, 0);
        } BLose()
    } BLose()

    lose_FnWMem_do_XnSys (&fix);
    lose_BitTable( &bt );

    dump_BitTable (of, sys->legit);
    dump_char_OFileB (of, '\n');

    { BLoopT( XnSz, i, sys->legit.sz )
        if (test_BitTable (sys->legit, i))
        {
            dump_char_OFileB (of, '+');
            dump_state_XnSys (of, sys, i);
            dump_char_OFileB (of, '\n');
        }
        else
        {
            dump_char_OFileB (of, '-');
            dump_state_XnSys (of, sys, i);
            dump_char_OFileB (of, '\n');
        }
    } BLose()

    flush_OFileB (of);
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

    Trit
detect_stabilizing (FnWMem_detect_livelock* tape,
                    const TableT(Xns) xns)
{
    bool missing = false;

    { BLoopT( XnSz, i, xns.sz )
        Bit legit = test_BitTable (*tape->legit, i);
        if (xns.s[i].sz == 0)
        {
            if (!legit)  missing = true;
        }
        else
        {
                /* No transitions from legit states (yet).*/
            if (legit)  return Nil;
        }
    } BLose()

    if (detect_livelock (tape, xns))  return Nil;

    return missing ? May : Yes;
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

    tape.sys = sys;
    tape.livelock_tape = cons1_FnWMem_detect_livelock (&sys->legit);
    tape.dostates_tape = cons1_FnWMem_do_XnSys (sys);
    tape.stabilizing = false;

    InitTable( tape.xns );
    GrowTable( tape.xns, sys->legit.sz );
    { BLoopT( XnSz, i, tape.xns.sz )
        InitTable( tape.xns.s[i] );
    } BLose()

    InitTable( tape.xn_stk );
    InitTable( tape.rules );
    tape.cached_nrules = 0;
    tape.rule_nwvbls = 0;
    tape.rule_nrvbls = 0;
    { BLoop( i, sys->pcs.sz )
        uint nwvbls = sys->pcs.s[i].nwvbls;
        uint nrvbls = sys->pcs.s[i].nrvbls;
        if (nwvbls > tape.rule_nwvbls)  tape.rule_nwvbls = nwvbls;
        if (nrvbls > tape.rule_nrvbls)  tape.rule_nrvbls = nrvbls;
    } BLose()

    return tape;
}

    void
lose_FnWMem_synsearch (FnWMem_synsearch* tape)
{
    lose_FnWMem_detect_livelock (&tape->livelock_tape);
    lose_FnWMem_do_XnSys (&tape->dostates_tape);

    { BLoopT( XnSz, i, tape->xns.sz )
        LoseTable( tape->xns.s[i] );
    } BLose()
    LoseTable( tape->xns );
    LoseTable( tape->xn_stk );

    { BLoop( i, tape->cached_nrules )
        LoseTable( tape->rules.s[i].p );
        LoseTable( tape->rules.s[i].q );
    } BLose()
    LoseTable( tape->rules );
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

    void
synsearch (FnWMem_synsearch* tape)
{
    const XnSys* restrict sys = tape->sys;
    XnRule* g;

    {
        Trit stabilizing =
            detect_stabilizing (&tape->livelock_tape, tape->xns);

        if (stabilizing == Nil)
        {
                /* DBog0( "NOPE" ); */
            return;
        }

        if (stabilizing == Yes)
        {
                /* DBog0( "BLACKJACK" ); */
            tape->stabilizing = true;
            return;
        }
    }
        /* DBog0( "HIT" ); */

    g = Grow1Table( tape->rules );

    if (tape->rules.sz > tape->cached_nrules)
    {
        g->pc = 0;
        InitTable( g->p );
        GrowTable( g->p, tape->rule_nrvbls );
        { BLoop( i, g->p.sz )
            g->p.s[i] = 0;
        } BLose()

        InitTable( g->q );
        GrowTable( g->q, tape->rule_nwvbls );
        { BLoop( i, g->q.sz )
            g->q.s[i] = 0;
        } BLose()

        ++ tape->cached_nrules;
    }

    if (tape->rules.sz > 1)
    {
        XnRule* tg = &tape->rules.s[tape->rules.sz-2];

        const XnPc* restrict pc = &sys->pcs.s[tg->pc];
        uint nwovbls = pc->vbls.sz - pc->nrvbls;
        uint off = 0;

        g->pc = tg->pc;
        CopyTable( g->p, tg->p );

        { BLoop( i, g->q.sz )
            g->q.s[i] = 0;
        } BLose()

        off = g->p.sz;
        while (off > 0)
        {
            -- off;
            if (g->p.s[off] < sys->vbls.s[pc->vbls.s[nwovbls + off]].max)
            {
                ++ g->p.s[off];
                off = g->p.sz;
                break;
            }
            g->p.s[off] = 0;
        }
        if (off == 0)  ++ g->pc;
    }

    for (; g->pc < sys->pcs.sz; ++g->pc)
    {
        const XnPc* restrict pc = &sys->pcs.s[g->pc];
        uint nwovbls = pc->vbls.sz - pc->nrvbls;
        uint off = 0;

        g->p.sz = pc->nrvbls;
        g->q.sz = pc->nwvbls;
        do
        {
            do
            {
                add_XnRule (tape, g);
                if (tape->rules.sz-1 < 7)
                {
                    OFileB* of = stderr_OFileB ();
                    dump_cstr_OFileB (of, " -- ");
                    dump_uint_OFileB (of, tape->rules.sz - 1);
                    dump_cstr_OFileB (of, " -- ");
                    dump_XnRule (of, g, sys);
                    dump_char_OFileB (of, '\n');
                    flush_OFileB (of);
                }


                synsearch (tape);
                if (tape->stabilizing)  return;
                back1_Xn (&tape->xns, &tape->xn_stk);

                g = TopTable( tape->rules );

                off = g->q.sz;
                while (off > 0)
                {
                    -- off;
                    if (g->q.s[off] < sys->vbls.s[pc->vbls.s[off]].max)
                    {
                        ++ g->q.s[off];
                        off = g->q.sz;
                        break;
                    }
                    g->q.s[off] = 0;
                }
            } while (off != 0);

            off = g->p.sz;
            while (off > 0)
            {
                -- off;
                if (g->p.s[off] < sys->vbls.s[pc->vbls.s[nwovbls + off]].max)
                {
                    ++ g->p.s[off];
                    off = g->p.sz;
                    break;
                }
                g->p.s[off] = 0;
            }
        } while (off != 0);
    }

    -- tape->rules.sz;
        /* DBog0( "BUST" ); */
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

    XnSys
sat3_XnSys ()
{
    Disj3 clauses[] = {
        {{ -2, -2, -2 }},
        {{ 1, 1, 1 }}
    };
    DeclTable( Disj3, cnf );
    const uint n = 1;
    DecloStack( XnSys, sys );

    *sys = dflt_XnSys ();
    cnf.s = clauses;
    cnf.sz = ArraySz( clauses );

    { BLoop( i, 3 )
        PushTable( sys->pcs, dflt_XnPc () );
    } BLose()
    PushTable( sys->pcs, dflt_XnPc () );

    { BLoop( r, 3 )
        const uint xi = sys->vbls.sz;
        const uint yi = sys->vbls.sz+1;
        XnVbl* x;
        XnVbl* y;

        GrowTable( sys->vbls, 2 );

        x = &sys->vbls.s[xi];
        y = &sys->vbls.s[yi];

        *x = dflt_XnVbl ();
        *y = dflt_XnVbl ();

        x->max = n-1;
        y->max = 1;

        assoc_XnSys (sys, r, xi, May);
        assoc_XnSys (sys, r, yi, Yes);
        assoc_XnSys (sys, 3, xi, May);
        assoc_XnSys (sys, 3, yi, May);
    } BLose()

    {
        DeclGrow1Table( XnVbl, sat, sys->vbls );
        *sat = dflt_XnVbl ();
        sat->max = 1;
    }

    { BLoop( r, 3 )
        assoc_XnSys (sys, r, sys->vbls.sz-1, May);
    } BLose()
    assoc_XnSys (sys, 3, sys->vbls.sz-1, Yes);

    accept_topology_XnSys (sys);

    sat3_legit_XnSys (sys, cnf);

    /*
    { BLoop( i, sys->legit.sz )
        if (test_BitTable (sys->legit, i))
            DBog1( "%u is true", i );
    } BLose()
    */
    DBog1( "size is %u", (uint) sys->legit.sz );

    return *sys;
}

#if 0
    void
dump_cnf_XnSys (FileB* f, const XnSys* sys)
{
    const XnSz nstates = size_XnSys (sys);
    const XnSz nxns = nstates * nstates;
    const uint nvbls = nstates + nxns;
    uint nclauses = 0;
}
#endif

    int
main ()
{
    DecloStack( XnSys, sys );
    init_sys_cx ();
    *sys = sat3_XnSys ();

    testfn_detect_livelock ();

    {
        FnWMem_synsearch tape = cons1_FnWMem_synsearch (sys);
        synsearch (&tape);
        if (tape.stabilizing)
        {
            DBog0( "Solution found! :)" );
            { BLoopT( XnSz, i, tape.rules.sz )
                dump_XnRule (stderr_OFileB (), &tape.rules.s[i], sys);
                dump_char_OFileB (stderr_OFileB (), '\n');
            } BLose()
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

