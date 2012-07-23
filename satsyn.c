
#include "cx/associa.h"
#include "cx/bittable.h"
#include "cx/fileb.h"
#include "cx/sys-cx.h"
#include "cx/table.h"

#include <assert.h>
#include <stdio.h>

static const bool DBog_WeakChk    = true;
static const bool DBog_AssertRule = true;
static const bool DBog_SearchStep = true;
static const bool DBog_QuickTrim = false;

static const bool SatSolve_Z3 = false;

typedef struct XnPc XnPc;
typedef struct XnVbl XnVbl;
typedef struct XnEVbl XnEVbl;
typedef struct XnRule XnRule;
typedef struct XnSys XnSys;
typedef ujint XnSz;
typedef byte DomSz;
typedef struct BoolLit BoolLit;
typedef struct CnfDisj CnfDisj;
typedef struct CnfFmla CnfFmla;
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
DeclTableT( BoolLit, BoolLit );
DeclTableT( CnfDisj, CnfDisj );
DeclTableT( Xns, TableT(XnSz) );
DeclTableT( XnSz2, XnSz2 );
DeclTableT( DomSz, DomSz );


struct XnSz2 { XnSz i; XnSz j; };

struct XnPc
{
    TableT(XnSz) vbls;
    XnSz nwvbls;

    XnSz nstates;  /* Same as /legit.sz/.*/

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
    TableT(XnSz2) influence_order;
    uint n_cached_rules;
    uint n_cached_may_rules;
    uint rule_nwvbls;
    uint rule_nrvbls;
    TableT(XnSz) legit_states;
    TableT(Xns) legit_xns;
};

struct BoolLit {
    Bit  val;
    uint vbl;
};
struct CnfDisj {
    TableT(BoolLit) lits;
};
struct CnfFmla {
    uint nvbls;
    TableT(ujint) idcs;  /* Clause indices.*/
    TableT(uint) vbls;  /* Clause variables.*/
    BitTable vals;  /* Clause values, negative (0) or positive (1).*/
};

    XnPc
dflt_XnPc ()
{
    XnPc pc;
    InitTable( pc.vbls );
    pc.nwvbls = 0;
    pc.nstates = 0;
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

    XnRule
cons3_XnRule (uint pcidx, uint np, uint nq)
{
    XnRule g = cons2_XnRule (np, nq);
    g.pc = pcidx;
    return g;
}

    XnRule
dup_XnRule (const XnRule* src)
{
    XnRule dst = dflt_XnRule ();
    dst.pc = src->pc;
    CopyTable( dst.p, src->p );
    CopyTable( dst.q, src->q );
    return dst;
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

    BoolLit
dflt2_BoolLit (bool val, uint vbl)
{
    BoolLit x;
    x.val = (val ? 1 : 0);
    x.vbl = vbl;
    return x;
}

    CnfDisj
dflt_CnfDisj ()
{
    CnfDisj disj;
    InitTable( disj.lits );
    return disj;
}

    void
lose_CnfDisj (CnfDisj* clause)
{
    LoseTable( clause->lits );
}

    void
app_CnfDisj (CnfDisj* clause, bool b, uint vbl)
{
    PushTable( clause->lits, dflt2_BoolLit (b, vbl) );
}

    CnfFmla
dflt_CnfFmla ()
{
    CnfFmla fmla;
    fmla.nvbls = 0;
    InitTable( fmla.idcs );
    InitTable( fmla.vbls );
    fmla.vals = dflt_BitTable ();
    return fmla;
}

    void
lose_CnfFmla (CnfFmla* fmla)
{
    LoseTable( fmla->idcs );
    LoseTable( fmla->vbls );
    lose_BitTable (&fmla->vals);
}

    void
app_CnfFmla (CnfFmla* fmla, const CnfDisj* clause)
{
    const ujint off = fmla->vbls.sz;
    Claim2( fmla->vbls.sz ,==, fmla->vals.sz );
    PushTable( fmla->idcs, off );
    GrowTable( fmla->vbls, clause->lits.sz );
    grow_BitTable (&fmla->vals, clause->lits.sz);
    { BLoop( i, clause->lits.sz )
        BoolLit lit = clause->lits.s[i];
        if (lit.val)  set1_BitTable (fmla->vals, off+i);
        else          set0_BitTable (fmla->vals, off+i);
        fmla->vbls.s[off+i] = lit.vbl;
    } BLose()
}

    void
clause_of_CnfFmla (CnfDisj* clause, const CnfFmla* fmla, ujint i)
{
    const ujint bel = (i+1 < fmla->idcs.sz
                       ? fmla->idcs.s[i+1]
                       : fmla->vbls.sz);
    clause->lits.sz = 0;
    for (i = fmla->idcs.s[i]; i < bel; ++i)
        app_CnfDisj (clause,
                     test_BitTable (fmla->vals, i),
                     fmla->vbls.s[i]);
}

qual_inline
    void
dump_BitTable (OFileB* f, const BitTable bt)
{
    ujint i;
    UFor( i, bt.sz )
        dump_char_OFileB (f, test_BitTable (bt, i) ? '1' : '0');
}


    TableT(XnSz)
wvbls_XnPc (const XnPc* pc)
{
    DeclTable( XnSz, t );
    t.s = pc->vbls.s;
    t.sz = pc->nwvbls;
    return t;
}

    TableT(XnSz)
rvbls_XnPc (const XnPc* pc)
{
    return pc->vbls;
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

        { BLoop( i, pc->vbls.sz-1 )
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
    sys->nstates = stepsz;
    sys->legit = cons2_BitTable (sys->nstates, 1);

    { BLoop( pcidx, sys->pcs.sz )
        XnPc* pc = &sys->pcs.s[pcidx];
        uint n;

        SizeTable( pc->rule_stepsz_p, pc->vbls.sz );
        SizeTable( pc->rule_stepsz_q, pc->nwvbls );

        stepsz = 1;

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

        pc->nstates = stepsz;

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

    EnsizeTable( g->q, pc->rule_stepsz_q.sz );
    { BLoop( i, g->q.sz )
        XnSz d = pc->rule_stepsz_q.s[i];
        g->q.s[i] = idx / d;
        idx = idx % d;
    } BLose()

    EnsizeTable( g->p, pc->rule_stepsz_p.sz );
    { BLoop( i, g->p.sz )
        XnSz d = pc->rule_stepsz_p.s[i];
        g->p.s[i] = idx / d;
        idx = idx % d;
    } BLose()
}

    XnSz
step_XnRule (const XnRule* g, const XnSys* sys)
{
    const XnPc* pc = &sys->pcs.s[g->pc];
    XnSz step = pc->rule_step;

    { BLoop( i, g->p.sz )
        step += g->p.s[i] * pc->rule_stepsz_p.s[i];
    } BLose()
    { BLoop( i, g->q.sz )
        step += g->q.s[i] * pc->rule_stepsz_q.s[i];
    } BLose()

    return step;
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
    const ujint n = sys->vbls.sz;

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

    op_BitTable (cycle, *tape->legit, BitOp_IDEN);
    op_BitTable (tested, *tape->legit, BitOp_IDEN);

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

    op_BitTable (tested, *tape->legit, BitOp_IDEN);

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
    InitTable( tape.influence_order );
    tape.n_cached_rules = 0;
    tape.n_cached_may_rules = 0;
    tape.rule_nwvbls = 0;
    tape.rule_nrvbls = 0;
    { BLoop( i, sys->pcs.sz )
        uint nwvbls = sys->pcs.s[i].nwvbls;
        uint nrvbls = sys->pcs.s[i].vbls.sz;
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

    LoseTable( tape->influence_order );

    LoseTable( tape->legit_states );

    { BLoopT( XnSz, i, tape->legit_xns.sz )
        LoseTable( tape->legit_xns.s[i] );
    } BLose()
    LoseTable( tape->legit_xns );
}

#define AppDelta( a, s0, s1 )  ((a) + (s1) - (s0))

    XnSz
apply1_XnRule (const XnRule* g, const XnSys* sys, XnSz sidx)
{
    const XnPc* pc = &sys->pcs.s[g->pc];
    { BLoop( i, g->q.sz )
        XnSz stepsz = sys->vbls.s[pc->vbls.s[i]].stepsz;
        sidx = AppDelta( sidx,
                         stepsz * g->p.s[i],
                         stepsz * g->q.s[i] );
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
        XnSz s1 = AppDelta( s0, sa, sb );
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

#if 1
    /* Only sort by the first member.*/
static
    int
cmp_XnSz2 (const void* pa, const void* pb)
{
    return cmp_XnSz (&((XnSz2*)pa)->i, &((XnSz2*)pb)->i);
}
#endif

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

        /* Note: Scrap variable /g/ is the most recent rule.*/
        /* Add preexisting rules.*/
    { BLoopT( XnSz, i, tape->rules.sz - 1 )
        add_XnRule (tape, &tape->rules.s[i]);
        if (0 == *TopTable( tape->xn_stk ))
        {
            DBog0( "Redundant rule given!" );
            back1_Xn (&tape->xns, &tape->xn_stk);
        }
    } BLose()


    { BLoopT( XnSz, i, sys->n_rule_steps )
            /* XnSz rule_step = i; */
        XnSz rule_step = sys->n_rule_steps - 1 - i;

        bool add = true;
        bool test_selfloop = true;
        DeclTable( XnSz, t );

        rule_XnSys (g, sys, rule_step);
        Claim2( rule_step ,==, step_XnRule (g, sys) );

        add_XnRule (tape, g);

        t.sz = *TopTable( tape->xn_stk );
        t.s = &tape->xn_stk.s[tape->xn_stk.sz - 1 - t.sz];

        if (t.sz == 0)  add = false;

        if (add)
        { BLoopT( XnSz, j, t.sz )
            const XnSz s0 = t.s[j];

                /* Do not add rules which cause
                 * bad transitions from legit states.
                 */
            if (test_BitTable (sys->legit, s0))
            {
                const XnSz s1 = *TopTable( tape->xns.s[s0] );
                const XnSz* elt;
                XnSz legit_idx;

                test_selfloop = false;

                elt = (XnSz*)
                    bsearch (&s0, tape->legit_states.s,
                             tape->legit_states.sz, sizeof(XnSz),
                             cmp_XnSz);

                legit_idx = IdxEltTable( tape->legit_states, elt );

                elt = (XnSz*)
                    bsearch (&s1,
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
        tape->n_cached_rules = tape->rules.sz;
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

    /**
     * Only allow self-disabling actions in /mayrules/.
     * The top of /tape->rules/ must be allocated for temp memory.
     */
    void
synsearch_quicktrim_mayrules (FnWMem_synsearch* tape, XnSz nadded)
{
    const XnSys* sys = tape->sys;
    TableT(XnSz)* may_rules = TopTable( tape->may_rules );
    XnSz off = 0;
    XnRule* g0 = TopTable( tape->rules );

    { BLoopT( XnSz, i, may_rules->sz )
        XnSz rule_step = may_rules->s[i];
        bool add = true;

        rule_XnSys (g0, sys, rule_step);

        Claim2( nadded+1 ,<=, tape->rules.sz );

        if (add)
        { BLoopT( XnSz, j, nadded )
            XnRule* g1 = &tape->rules.s[tape->rules.sz-1-nadded+j];
            bool match = (g0->pc == g1->pc);

            if (match)
            { BLoop( k, g0->p.sz - g0->q.sz )
                match = (g0->p.s[k+g0->q.sz] == g1->p.s[k+g0->q.sz]);
                if (!match)  break;
            } BLose()

            if (match)
            {
                    /* Can't have two actions with the same guard.*/
                match = true;
                { BLoop( k, g0->q.sz )
                    match = (g0->q.s[k] == g1->p.s[k]);
                    if (!match)  break;
                } BLose()
                add = !match;
                if (!add)  break;

                    /* Remove actions which would not be self-disabling.*/
                match = true;
                { BLoop( k, g0->q.sz )
                    match = (g0->p.s[k] == g1->p.s[k]);
                    if (!match)  break;
                } BLose()
                add = !match;
                if (!add)  break;
            }
        } BLose()

        if (add)
        {
            may_rules->s[off] = may_rules->s[i];
            ++ off;
        }
    } BLose()
    if (DBog_QuickTrim)
        DBog1( "Removed:%lu", may_rules->sz - off );
    may_rules->sz = off;
}

    void
synsearch_trim (FnWMem_synsearch* tape)
{
    const XnSys* sys = tape->sys;
    TableT(XnSz)* may_rules = TopTable( tape->may_rules );
    XnRule* g = TopTable( tape->rules );

        /* Trim down the next possible steps.*/
    if (true)
    {
        XnSz off = 0;

        { BLoopT( XnSz, i, may_rules->sz )
            Trit stabilizing;
            XnSz rule_step = may_rules->s[i];
            bool tolegit = false;
            ujint nresolved = 0;

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
                DeclTable( XnSz, t );
                t.sz = *TopTable( tape->xn_stk );
                t.s = &tape->xn_stk.s[tape->xn_stk.sz - 1 - t.sz];

                Claim2( t.sz ,>, 0 );

                { BLoopT( XnSz, j, t.sz )
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
                        if (test_BitTable (sys->legit, s1))  tolegit = true;
                    }
                } BLose()

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

            back1_Xn (&tape->xns, &tape->xn_stk);
        } BLose()
        may_rules->sz = off;
    }

    {
        qsort (tape->influence_order.s,
               tape->influence_order.sz,
               sizeof(*tape->influence_order.s),
               cmp_XnSz2);
        { BLoopT( XnSz, i, tape->influence_order.sz )
                /* XnSz idx = tape->influence_order.sz - 1 - i; */
            XnSz idx = i;
            may_rules->s[i] = tape->influence_order.s[idx].j;
        } BLose()
        tape->influence_order.sz = 0;
    }
}

    bool
synsearch_check_weak (FnWMem_synsearch* tape, XnSz* ret_nreqrules)
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
            if (DBog_WeakChk)
                DBog1( "Not weakly stabilizing at depth %u.",
                       tape->may_rules.sz-1 );
            return false;
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

    *ret_nreqrules = nreqrules;
    return true;
}

    /**
     * TODO: Make sure this works when the protocol has
     * transitions defined in the legit states.
     **/
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

    if (tape->may_rules.sz == 1)
    {
        Trit stabilizing;
        if (all_BitTable (sys->legit))
        {
            tape->stabilizing = true;
            CopyTable( tape->rules, sys->legit_rules );
            -- tape->rules.sz;
            return;
        }

        stabilizing = detect_strong_convergence (tape);
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
        set_may_rules (tape, may_rules, g);
        synsearch_quicktrim_mayrules (tape, tape->rules.sz-1);
    }
    else
    {
        CopyTable( *may_rules, *(may_rules - 1) );
        synsearch_quicktrim_mayrules (tape, 1);
    }

    synsearch_trim (tape);
    if (tape->stabilizing)  return;

    while (may_rules->sz > 0)
    {
        if (!synsearch_check_weak (tape, &nreqrules))  break;
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
                g = grow1_rules_synsearch (tape);
                synsearch_quicktrim_mayrules (tape, nreqrules);
                -- tape->rules.sz;
                g = TopTable( tape->rules );
                synsearch (tape);
                if (tape->stabilizing)  return;
            }

            { BLoop( i, nreqrules )
                back1_Xn (&tape->xns, &tape->xn_stk);
            } BLose()
            break;
        }
        else
        {
            XnSz rule_step = *TopTable( *may_rules );
            -- may_rules->sz;
            rule_XnSys (g, sys, rule_step);

            add_XnRule (tape, g);
            if (DBog_SearchStep
                || tape->may_rules.sz-1 < 40)
            {
                OFileB* of = stderr_OFileB ();
                dump_cstr_OFileB (of, " -- ");
                dump_uint_OFileB (of, tape->may_rules.sz - 1);
                dump_cstr_OFileB (of, " -- ");
                dump_uint_OFileB (of, may_rules->sz);
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
                  XnSys* sys,
                  TableT(CnfDisj) cnf,
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

            op_BitTable (bt, bt, BitOp_NOT);

            set1_BitTable (fix->fixed, y_idcs[lo]);
            set1_BitTable (fix->fixed, y_idcs[hi]);
            { BLoop( val, 2 )
                fix->vals[y_idcs[lo]] = val;
                fix->vals[y_idcs[hi]] = val;
                do_XnSys (fix, bt);
            } BLose()
            set0_BitTable (fix->fixed, y_idcs[lo]);
            set0_BitTable (fix->fixed, y_idcs[hi]);

            op_BitTable (sys->legit, bt, BitOp_AND);
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
            BoolLit lits[3];

            { BLoop( i, 3 )
                byte idx = perms[permi][i];
                lits[i] = cnf.s[ci].lits.s[idx];
            } BLose()

            { BLoop( lo, nwindows )

                wipe_BitTable (bt, 0);

                    /* Get variables on the stack.*/
                { BLoop( i, 3 )
                    const uint pcidx = x_idcs[(lo + i) % npcs];

                    set1_BitTable (fix->fixed, pcidx);
                    fix->vals[pcidx] = (DomSz) lits[i].vbl;
                } BLose()

                do_XnSys (fix, bt);
                op_BitTable (bt, bt, BitOp_NOT);

                { BLoop( i, 3 )
                    const uint pcidx = y_idcs[(lo + i) % npcs];

                    set1_BitTable (fix->fixed, pcidx);
                    fix->vals[pcidx] = lits[i].val;
                    do_XnSys (fix, bt);
                    set0_BitTable (fix->fixed, pcidx);
                } BLose()

                op_BitTable (sys->legit, bt, BitOp_AND);

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

    void
dump_dimacs_CnfFmla (OFileB* of, const CnfFmla* fmla)
{
    DecloStack1( CnfDisj, clause, dflt_CnfDisj () );
    printf_OFileB (of, "p cnf %u %u\n",
                   (uint) fmla->nvbls,
                   (uint) fmla->idcs.sz);
    { BLoop( i, fmla->idcs.sz )
        clause_of_CnfFmla (clause, fmla, i);
        { BLoop( j, clause->lits.sz )
            if (!clause->lits.s[j].val)
                dump_char_OFileB (of, '-');
            dump_uint_OFileB (of, 1+clause->lits.s[j].vbl);
            dump_char_OFileB (of, ' ');
        } BLose()
        dump_cstr_OFileB (of, "0\n");
    } BLose()
    lose_CnfDisj (clause);
}

    void
load_dimacs_result (XFileB* xf, bool* sat, BitTable evs)
{
    const char* line = getline_XFileB (xf);
    wipe_BitTable (evs, 0);
    if (0 == strcmp (line, "UNSAT") ||
        0 == strcmp (line, "unsat"))
    {
        *sat = false;
    }
    else
    {
        int v;
        bool good;
        *sat = true;

        good = load_int_XFileB (xf, &v);
        while (good)
        {
            if      (v > 0)  set1_BitTable (evs, +v-1);
            else if (v < 0)  set0_BitTable (evs, -v-1);
            good = load_int_XFileB (xf, &v);
        }
    }
}

    void
extl_solve_CnfFmla (CnfFmla* fmla, bool* sat, BitTable evs)
{
    DecloStack( FileB, fb );
    init_FileB (fb);
    seto_FileB (fb, true);
    open_FileB (fb, 0, "sat.in");
    dump_dimacs_CnfFmla (&fb->xo, fmla);
    close_FileB (fb);

    lose_CnfFmla (fmla);
    *fmla = dflt_CnfFmla ();

    if (SatSolve_Z3)
        system ("z3 -dimacs sat.in > sat.out");
    else
        system ("minisat -verb=0 sat.in sat.out");

    seto_FileB (fb, false);
    open_FileB (fb, 0, "sat.out");
    load_dimacs_result (&fb->xo, sat, evs);
    lose_FileB (fb);
}


    XnSys
sat3_XnSys (const CnfFmla* fmla)
{
    uint x_idcs[3];
    uint y_idcs[3];
    uint sat_idx;
    DecloStack( XnSys, sys );
    OFileB name = dflt_OFileB ();

    *sys = dflt_XnSys ();

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

        x->max = fmla->nvbls-1;
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
        DeclTable( CnfDisj, clauses );
        DecloStack1( FnWMem_do_XnSys, fix, cons1_FnWMem_do_XnSys (sys) );
        BitTable bt = cons2_BitTable (sys->legit.sz, 0);

        { BUjFor( i, fmla->idcs.sz )
            CnfDisj clause = dflt_CnfDisj ();
            clause_of_CnfFmla (&clause, fmla, i);
            PushTable( clauses, clause );
        } BLose()

        fix->vals[sat_idx] = 1;
        set1_BitTable (fix->fixed, sat_idx);
        do_XnSys (fix, bt);
        op_BitTable (sys->legit, bt, BitOp_AND);

        sat3_legit_XnSys (fix, bt, sys, clauses, 3, x_idcs, y_idcs);

        lose_BitTable (&bt);
        lose_FnWMem_do_XnSys (fix);
        { BUjFor( i, clauses.sz )
            lose_CnfDisj (&clauses.s[i]);
        } BLose()
        LoseTable( clauses );
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
sat3_ring_XnSys (const CnfFmla* fmla, const bool use_sat)
{
    uint x_idcs[5];
    uint y_idcs[ArraySz( x_idcs )];
    uint sat_idcs[ArraySz( x_idcs )];
    const uint npcs = ArraySz( x_idcs );
    DecloStack( XnSys, sys );
    OFileB name = dflt_OFileB ();

    *sys = dflt_XnSys ();

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

    if (use_sat)
    { BLoop( r, npcs )
        sat_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, dflt_XnVbl () );
    } BLose()

    { BLoop( r, npcs )
        XnVbl* x = &sys->vbls.s[x_idcs[r]];
        XnVbl* y = &sys->vbls.s[y_idcs[r]];

        x->max = fmla->nvbls - 1;
        y->max = (use_sat ? 1 : 2);

        flush_OFileB (&name);
        printf_OFileB (&name, "x%u", r);
        CopyTable( x->name, name.buf );

        flush_OFileB (&name);
        printf_OFileB (&name, "y%u", r);
        CopyTable( y->name, name.buf );


            /* Process r */
        assoc_XnSys (sys, r, x_idcs[r], May);
        assoc_XnSys (sys, r, y_idcs[r], Yes);

            /* Process r+1 */
        assoc_XnSys (sys, (r + 1) % npcs, x_idcs[r], May);
        assoc_XnSys (sys, (r + 1) % npcs, y_idcs[r], May);

            /* Process r-1 */
        assoc_XnSys (sys, (r + npcs - 1) % npcs, x_idcs[r], May);
        assoc_XnSys (sys, (r + npcs - 1) % npcs, y_idcs[r], May);
    } BLose()

    if (use_sat)
    { BLoop( r, npcs )
        XnVbl* sat = &sys->vbls.s[sat_idcs[r]];
        sat->max = 1;

        flush_OFileB (&name);
        printf_OFileB (&name, "sat%u", r);
        CopyTable( sat->name, name.buf );
            /* Process r */
        assoc_XnSys (sys, r, sat_idcs[r], Yes);
            /* Process r+1 */
        assoc_XnSys (sys, (r + 1) % npcs, sat_idcs[r], May);
            /* Process r-1 */
        assoc_XnSys (sys, (r + npcs - 1) % npcs, sat_idcs[r], May);
    } BLose()

    lose_OFileB (&name);

    accept_topology_XnSys (sys);

    {
        DeclTable( CnfDisj, clauses );
        DecloStack1( FnWMem_do_XnSys, fix, cons1_FnWMem_do_XnSys (sys) );
        BitTable bt = cons2_BitTable (sys->legit.sz, 0);

        { BUjFor( i, fmla->idcs.sz )
            CnfDisj clause = dflt_CnfDisj ();
            clause_of_CnfFmla (&clause, fmla, i);
            PushTable( clauses, clause );
        } BLose()

        if (use_sat)
        {
            { BLoop( i, npcs )
                fix->vals[sat_idcs[i]] = 1;
                set1_BitTable (fix->fixed, sat_idcs[i]);
            } BLose()
            do_XnSys (fix, bt);
            op_BitTable (sys->legit, bt, BitOp_AND);
        }
        else
        {
            { BLoop( i, npcs )
                set1_BitTable (fix->fixed, y_idcs[i]);
                fix->vals[y_idcs[i]] = 2;
                wipe_BitTable (bt, 0);
                do_XnSys (fix, bt);
                op_BitTable (bt, bt, BitOp_NOT);
                op_BitTable (sys->legit, bt, BitOp_AND);
                set0_BitTable (fix->fixed, y_idcs[i]);
            } BLose()
        }

        wipe_BitTable (bt, 0);

        sat3_legit_XnSys (fix, bt, sys, clauses, npcs, x_idcs, y_idcs);

        lose_BitTable (&bt);
        lose_FnWMem_do_XnSys (fix);
        { BUjFor( i, clauses.sz )
            lose_CnfDisj (&clauses.s[i]);
        } BLose()
        LoseTable( clauses );
    }

    return *sys;
}

    void
sat3_soln_XnSys (TableT(XnRule)* rules,
                 const BitTable evs, const XnSys* sys)
{
    { BLoop( pcidx, 3 )
        const XnPc* pc = &sys->pcs.s[pcidx];
        uint x_idx = 0;
        uint y_idx = 0;
        uint sat_idx = 0;
        const XnVbl* x_vbl;
        const XnVbl* y_vbl;

        { BLoop( i, 3 )
            char c = sys->vbls.s[pc->vbls.s[i]].name.s[0];
            if (c == 'x')  x_idx = i;
            if (c == 'y')  y_idx = i;
            if (c == 's')  sat_idx = i;
        } BLose()

        x_vbl = &sys->vbls.s[pc->vbls.s[x_idx]];
        y_vbl = &sys->vbls.s[pc->vbls.s[y_idx]];

        { BLoop( x_val, (uint) (x_vbl->max + 1) )
            XnRule g = cons2_XnRule (3, 1);
            Bit y_val = test_BitTable (evs, x_val);

            g.pc = pcidx;
            g.p.s[x_idx] = x_val;
            g.p.s[y_idx] = !y_val;
            g.p.s[sat_idx] = 0;
            g.q.s[y_idx] = y_val;
            PushTable( *rules, g );
        } BLose()
    } BLose()
}

    void
sat3_ring_soln_XnSys (TableT(XnRule)* rules,
                      const BitTable evs, const XnSys* sys,
                      const CnfFmla* fmla)
{
    const bool use_sat = (sys->pcs.s[0].nwvbls == 2);
    CnfDisj clause = dflt_CnfDisj ();
    DeclTable( XnSz, x_idcs );
    DeclTable( XnSz, y_idcs );
    DeclTable( XnSz, sat_idcs );

    EnsizeTable( x_idcs, sys->pcs.sz );
    EnsizeTable( y_idcs, sys->pcs.sz );
    EnsizeTable( sat_idcs, sys->pcs.sz );
    { BLoop( pcidx, sys->pcs.sz )
        x_idcs.s[pcidx] = sys->vbls.sz;
        y_idcs.s[pcidx] = sys->vbls.sz;
        sat_idcs.s[pcidx] = sys->vbls.sz;
    } BLose()

    { BLoop( i, sys->vbls.sz )
        const XnVbl* x = &sys->vbls.s[i];
        char c = x->name.s[0];
        uint pcidx = 0;
        uint mid = x->pcs.s[2];
        uint min = mid;
        uint max = mid;

        Claim2( x->pcs.sz ,==, 3 );
        { BLoop( j, 2 )
            uint a = x->pcs.s[j];
            if      (a < min) { mid = min; min = a; }
            else if (a > max) { mid = max; max = a; }
            else              { mid = a; }
        } BLose()
        Claim2( min ,<, mid );
        Claim2( mid ,<, max );

        if (mid == min + 1)
        {
            if (mid == max - 1)  pcidx = mid;
            else                 pcidx = min;
        }
        else                     pcidx = max;

        if (c == 'x')  x_idcs.s[pcidx] = i;
        if (c == 'y')  y_idcs.s[pcidx] = i;
        if (c == 's')  sat_idcs.s[pcidx] = i;
        Claim( c == 'x' || c == 'y' || c == 's' );
    } BLose()

    { BLoop( pcidx, sys->pcs.sz )
        Claim2( x_idcs.s[pcidx] ,<, sys->vbls.sz );
        Claim2( y_idcs.s[pcidx] ,<, sys->vbls.sz );
        if (use_sat)
            Claim2( sat_idcs.s[pcidx] ,<, sys->vbls.sz );
    } BLose()

    { BLoop( pcidx, sys->pcs.sz )
        const uint npcs = sys->pcs.sz;
        const uint oh_pcidx = pcidx;
        const uint hi_pcidx = (oh_pcidx + 1) % npcs;
        const uint lo_pcidx = (oh_pcidx + npcs - 1) % npcs;

        const XnPc* pc = &sys->pcs.s[pcidx];
        const XnSz n_rule_steps =
            pc->rule_stepsz_q.s[0] *
            ((uint) sys->vbls.s[pc->vbls.s[0]].max + 1);
        XnRule g = cons3_XnRule (pcidx, pc->vbls.sz, pc->nwvbls);
        uint x_pidcs[3];
        uint y_pidcs[3];
        uint sat_pidcs[3];
        TableT(XnSz) vbls;

        vbls = pc->vbls;
        if (!use_sat)  Claim2( vbls.sz ,==, 6 );
        else           Claim2( vbls.sz ,==, 9 );

        { BLoop( i, 3 )
            x_pidcs[i] = vbls.sz;
            y_pidcs[i] = vbls.sz;
            sat_pidcs[i] = vbls.sz;
        } BLose()

        { BLoop( i, vbls.sz )
            if      (vbls.s[i] == x_idcs.s[oh_pcidx])  x_pidcs[0] = i;
            else if (vbls.s[i] == x_idcs.s[lo_pcidx])  x_pidcs[1] = i;
            else if (vbls.s[i] == x_idcs.s[hi_pcidx])  x_pidcs[2] = i;
            else if (vbls.s[i] == y_idcs.s[oh_pcidx])  y_pidcs[0] = i;
            else if (vbls.s[i] == y_idcs.s[lo_pcidx])  y_pidcs[1] = i;
            else if (vbls.s[i] == y_idcs.s[hi_pcidx])  y_pidcs[2] = i;
            else if (!use_sat)  Claim( 0 );
            else if (vbls.s[i] == sat_idcs.s[oh_pcidx])  sat_pidcs[0] = i;
            else if (vbls.s[i] == sat_idcs.s[lo_pcidx])  sat_pidcs[1] = i;
            else if (vbls.s[i] == sat_idcs.s[hi_pcidx])  sat_pidcs[2] = i;
            else  Claim( 0 );
        } BLose()

        { BLoop( i, 3 )
            Claim2( x_pidcs[i] ,<, vbls.sz );
            Claim2( y_pidcs[i] ,<, vbls.sz );
            if (use_sat)
                Claim2( sat_pidcs[i] ,<, vbls.sz );
        } BLose()

        { BLoopT( XnSz, rule_step_idx, n_rule_steps )
            const XnSz rule_step = pc->rule_step + rule_step_idx;
            bool add = false;
            Bit soln_y = test_BitTable (evs, g.p.s[x_pidcs[0]]);
            Bit lo_soln_y = test_BitTable (evs, g.p.s[x_pidcs[1]]);
            Bit hi_soln_y = test_BitTable (evs, g.p.s[x_pidcs[2]]);
            bool xy_legit = true;

            rule_XnSys (&g, sys, rule_step);

            { BLoop( i, fmla->idcs.sz )
                bool allin = true;
                bool satisfied = false;

                clause.lits.sz = 0;
                clause_of_CnfFmla (&clause, fmla, i);

                { BLoop( j, 3 )
                    bool found = false;

                    { BLoop( k, 3 )
                        if (g.p.s[x_pidcs[j]] == clause.lits.s[j].vbl)
                        {
                            if (g.p.s[y_pidcs[j]] == clause.lits.s[j].val)
                                satisfied = true;
                            found = true;
                        }
                    } BLose()

                    if (satisfied)  break;
                    if (!found)
                    {
                        allin = false;
                        break;
                    }
                } BLose()

                if (allin && !satisfied)
                {
                    xy_legit = false;
                    break;
                }
            } BLose()

            if (use_sat &&
                (!xy_legit ||
                 g.p.s[sat_pidcs[0]] == 0 ||
                 g.p.s[sat_pidcs[1]] == 0 ||
                 g.p.s[sat_pidcs[2]] == 0)
                && ((g.p.s[y_pidcs[0]] != soln_y) ||
                    (g.p.s[sat_pidcs[0]] == 0))
                && (g.q.s[y_pidcs[0]] == soln_y)
                && (g.q.s[sat_pidcs[0]] == 1)
                && ((g.p.s[x_pidcs[1]] != g.p.s[x_pidcs[2]])
                    || (((g.p.s[y_pidcs[1]] == lo_soln_y)
                         || (g.p.s[sat_pidcs[1]] == 0))
                        &&
                        ((g.p.s[y_pidcs[2]] == hi_soln_y)
                         || (g.p.s[sat_pidcs[2]] == 0)))))
            {
                add = true;
            }
            if (0 && !use_sat
                && (g.q.s[y_pidcs[0]] == soln_y)
                && ((g.p.s[y_pidcs[0]] == 2)
                    || (!xy_legit && (g.p.s[y_pidcs[0]] != soln_y)))
                && ((g.p.s[y_pidcs[1]] == lo_soln_y)
                    || (g.p.s[y_pidcs[1]] == 2))
                && ((g.p.s[y_pidcs[2]] == hi_soln_y)
                    || (g.p.s[y_pidcs[2]] == 2)))
            {
                add = true;
            }
            if (!add && !use_sat
                && (g.q.s[y_pidcs[0]] == 2)
                && (!xy_legit ||
                    ((g.p.s[x_pidcs[1]] == g.p.s[x_pidcs[2]])
                     && (g.p.s[y_pidcs[1]] != g.p.s[y_pidcs[2]])))
                && (g.p.s[y_pidcs[0]] != 2)
                && (((g.p.s[y_pidcs[1]] != 2)
                     && (g.p.s[y_pidcs[1]] != lo_soln_y))
                    ||
                    ((g.p.s[y_pidcs[2]] != 2)
                     && (g.p.s[y_pidcs[2]] != hi_soln_y))))
            {
                add = true;
            }


            if (add)  PushTable( *rules, dup_XnRule (&g) );
        } BLose()

        lose_XnRule (&g);
    } BLose()

    LoseTable( x_idcs );
    LoseTable( y_idcs );
    LoseTable( sat_idcs );
    lose_CnfDisj (&clause);
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

    {
        bool found = false;
        XnSz i;
        UFor( i, rules.sz )
            if (rules.s[i].pc == pcidx)
                found = true;
        if (!found)
        {
            dump_cstr_OFileB (of, "skip;\n}\n\n");
            return;
        }
    }

    dump_cstr_OFileB (of, "end_");
    dump_uint_OFileB (of, pcidx);
    dump_cstr_OFileB (of, ":\n");
    dump_cstr_OFileB (of, "do\n");
    { BLoopT( XnSz, i, rules.sz )
        const XnRule* g = &rules.s[i];
        if (g->pc == pcidx)
        {
            dump_cstr_OFileB (of, ":: atomic {");
            dump_promela_XnRule (of, g, sys);
            dump_cstr_OFileB (of, "};\n");
        }
    } BLose()
    dump_cstr_OFileB (of, "od;\n");
    dump_cstr_OFileB (of, "}\n\n");
    
}

    void
dump_promela (OFileB* of, const XnSys* sys, const TableT(XnRule) rules)
{
#define dumpl(s)  dump_cstr_OFileB(of, s); dump_char_OFileB(of, '\n')
    dumpl( "/*** Use acceptance cycle check with the LTL claim for a full verification!" );
    dumpl( " *** Assertions, end states, and progress conditions are present to help debugging." );
    dumpl( " *** A safety check and liveness check (BOTH WITH LTL CLAIM DISABLED) should be" );
    dumpl( " *** equivalent to verifying the LTL claim holds via the acceptance cycle check." );
    dumpl( " ***/" );
    dumpl( "bool Legit = false;" );
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

    { BLoop( i, sys->pcs.sz )
        dump_promela_pc (of, &sys->pcs.s[i], sys, rules);
    } BLose()

    dumpl( "init {" );
    { BLoop( i, sys->vbls.sz )
        const XnVbl* x = &sys->vbls.s[i];
        dump_promela_select (of, x);
    } BLose()

    { BLoop( i, sys->pcs.sz )
        dump_cstr_OFileB (of, "run P");
        dump_uint_OFileB (of, i);
        dump_cstr_OFileB (of, " ();\n");
    } BLose()

    dumpl( "if" );
    { BLoopT( XnSz, i, sys->legit.sz )
        if (test_BitTable (sys->legit, i))
        {
            dump_cstr_OFileB (of, ":: ");
            dump_promela_state_XnSys (of, sys, i);
            dump_cstr_OFileB (of, " -> skip;\n");
        }
    } BLose()
    dumpl( "fi;" );

    dumpl( "Legit = true;" );
    dumpl( "progress: skip;" );

    dumpl( "end:" );
    dumpl( "if" );
    { BLoopT( XnSz, i, sys->legit.sz )
        if (!test_BitTable (sys->legit, i))
        {
            dump_cstr_OFileB (of, ":: ");
            dump_promela_state_XnSys (of, sys, i);
            dump_cstr_OFileB (of, " -> skip;\n");
        }
    } BLose()
    dumpl( "fi;" );
    dumpl( "Legit = false;" );
    dumpl( "assert(0);" );
    dumpl( "}" );

    dumpl( "ltl {" );
    dumpl( "<> Legit && [] (Legit -> [] Legit)" );
    dumpl( "}" );
#undef dumpl
}

    Trit
swapped_XnSz (const XnSz* a, const XnSz* b)
{
    return (*a < *b ? Nil : (*a > *b ? Yes : May));
}

    Trit
swapped_XnSz2 (const XnSz2* a, const XnSz2* b)
{
    const Trit swapped = swapped_XnSz (&a->i, &b->i);
    return (swapped == May
            ? swapped_XnSz (&a->j, &b->j)
            : swapped);
}

    /**
     * Reduce the AddConvergence problem to SAT and solve it.
     *
     * TODO: Make this work when the protocol has
     * transitions defined in the legit states.
     **/
    void
synsearch_sat (FnWMem_synsearch* tape)
{
    DeclTableT( XnInfo, struct { ujint idx; CnfDisj impl; } );
    DeclTableT( State, struct { TableT(XnSz) tx; TableT(XnSz) to; } );

    DecloStack( Associa, lstate_map );
    DecloStack( Associa, xnmap );
    DeclTable( State, states );
    DecloStack1( CnfFmla, fmla, dflt_CnfFmla () );
    DeclTable( XnInfo, xns );
    DecloStack( Associa, pathmap );
    DecloStack1( CnfDisj, clause, dflt_CnfDisj () );

    const XnSys* restrict sys = tape->sys;
    XnRule* g;
    TableT(XnSz)* may_rules;

    init3_Associa (lstate_map, sizeof(XnSz), sizeof(TableT(ujint)),
                   (SwappedFn) swapped_XnSz);
    init3_Associa (xnmap, sizeof(XnSz2), sizeof(ujint),
                   (SwappedFn) swapped_XnSz2);
    init3_Associa (pathmap, sizeof(XnSz2), sizeof(ujint),
                   (SwappedFn) swapped_XnSz2);

    g = grow1_rules_synsearch (tape);
    may_rules = grow1_may_rules_synsearch (tape);

    may_rules->sz = 0;

    if (all_BitTable (sys->legit))
    {
        tape->stabilizing = true;
        CopyTable( tape->rules, sys->legit_rules );
        -- tape->rules.sz;
        return;
    }
    else
    {
        Trit stabilizing = detect_strong_convergence (tape);
        if (stabilizing != May)
        {
            if (stabilizing == Yes)
                tape->stabilizing = true;
            if (stabilizing == Nil)
                DBog0( "Hint protocol has a livelock!" );
            -- tape->rules.sz;
            return;
        }
    }

    set_may_rules (tape, may_rules, g);
    synsearch_quicktrim_mayrules (tape, tape->rules.sz-1);
    synsearch_trim (tape);
    if (tape->stabilizing)  return;

    { BUjFor( i, tape->rules.sz-1 )
        XnSz step = step_XnRule (&tape->rules.s[i], sys);
        PushTable( *may_rules, step );
    } BLose()
    tape->rules.sz = 1;
    g = &tape->rules.s[0];

    while (tape->xn_stk.sz > 0)
        back1_Xn (&tape->xns, &tape->xn_stk);

    AffyTable( states, sys->nstates );
    states.sz = sys->nstates;
    { BUjFor( i, states.sz )
        InitTable( states.s[i].to );
        InitTable( states.s[i].tx );
    } BLose()

    fmla->nvbls = may_rules->sz;
    { BUjFor( i, may_rules->sz )
        rule_XnSys (g, sys, may_rules->s[i]);
        add_XnRule (tape, g);
        { BUjFor( j, *TopTable(tape->xn_stk) )
            XnSz2 t;
            bool added = false;
            TableElT(XnInfo)* xn;
            Assoc* assoc;
            t.i = tape->xn_stk.s[tape->xn_stk.sz-2-j];
            t.j = *TopTable( tape->xns.s[t.i] );
            Claim2( t.i ,<, sys->nstates );
            Claim2( t.j ,<, sys->nstates );
            assoc = ensure1_Associa (xnmap, &t, &added);
            if (added)
            {
                ujint idx = xns.sz;
                val_fo_Assoc (assoc, &idx);
                xn = Grow1Table( xns );
                xn->idx = fmla->nvbls ++;
                xn->impl = dflt_CnfDisj ();
                app_CnfDisj (&xn->impl, false, xn->idx);
                PushTable( states.s[t.j].tx, t.i );
                PushTable( states.s[t.i].to, t.j );
            }
            else
            {
                ujint idx = *(ujint*) val_of_Assoc (assoc);
                xn = &xns.s[idx];
            }
            app_CnfDisj (&xn->impl, true, i);

            clause->lits.sz = 0;
            app_CnfDisj (clause, false, i);
            app_CnfDisj (clause, true, xn->idx);
            app_CnfFmla (fmla, clause);
        } BLose()
        back1_Xn (&tape->xns, &tape->xn_stk);
        
        { BLoop( qi, g->q.sz )
            g->q.s[qi] = 0;
        } BLose()

        {
            XnSz step = step_XnRule (g, sys);
            bool added = false;
            Assoc* assoc = ensure1_Associa (lstate_map, &step, &added);
            TableT(ujint)* rules = (TableT(ujint)*) val_of_Assoc (assoc);
            if (added)  InitTable( *rules );
            PushTable( *rules, i );
        }
    } BLose()

    { BUjFor( i, xns.sz )
        CnfDisj* clause = &xns.s[i].impl;
        app_CnfFmla (fmla, clause);
        lose_CnfDisj (clause);
    } BLose()

    { BUjFor( si, lstate_map->nodes.sz )
        TableT(ujint)* rules = (TableT(ujint)*)
            elt_Table (&lstate_map->vals, si);
        { BUjFor( i, rules->sz )
            { BUjFor( j, i )
                clause->lits.sz = 0;
                app_CnfDisj (clause, false, rules->s[i]);
                app_CnfDisj (clause, false, rules->s[j]);
                app_CnfFmla (fmla, clause);
            } BLose()
        } BLose()
        LoseTable( *rules );
    } BLose()
    lose_Associa (lstate_map);

    { BUjFor( i, states.sz )
        if (!test_BitTable (sys->legit, i))
        {
            TableElT(State)* state = &states.s[i];

            if (state->to.sz == 0)
                DBog0( "Illegit state without outgoing transitions!!!!" );

                /* Deadlock freedom clause.*/
            clause->lits.sz = 0;
            { BUjFor( j, state->to.sz )
                XnSz2 t;
                Assoc* assoc;
                ujint idx;
                t.i = i;
                t.j = state->to.s[j];
                assoc = lookup_Associa (xnmap, &t);
                Claim( assoc );
                idx = xns.s[*(ujint*) val_of_Assoc (assoc)].idx;
                app_CnfDisj (clause, true, idx);
            } BLose()

            app_CnfFmla (fmla, clause);
        }

        { BUjFor( j, states.sz )
            if (states.s[i].to.sz > 0 && states.s[j].tx.sz > 0)
            {
                XnSz2 xn;
                ujint idx = fmla->nvbls ++;
                xn.i = i;
                xn.j = j;
                insert_Associa (pathmap, &xn, &idx);

                if (i == j)
                {
                    clause->lits.sz = 0;
                    app_CnfDisj (clause, false, idx);
                    app_CnfFmla (fmla, clause);
                }
            }
        } BLose()
    } BLose()

    { BUjFor( path_idx, pathmap->nodes.sz )
        DecloStack1( CnfDisj, path_clause, dflt_CnfDisj () );
        XnSz2 p = *(XnSz2*) elt_Table (&pathmap->keys, path_idx);
        ujint p_ij = *(ujint*) elt_Table (&pathmap->vals, path_idx);
        TableElT(State) state = states.s[p.j];

        app_CnfDisj (path_clause, false, p_ij);

        { BUjFor( k_idx, state.tx.sz )
            Assoc* assoc;
            ujint k = state.tx.s[k_idx];
            ujint q_ikj;
            if (k == p.i)
            {
                    /* In this case, just let q_{ikj} = t_{ij}.*/
                assoc = lookup_Associa (xnmap, &p);
                Claim( assoc );
                q_ikj = xns.s[*(ujint*) val_of_Assoc (assoc)].idx;
            }
            else
            {
                XnSz2 xn;
                ujint p_ik, t_kj;

                xn.i = p.i;
                xn.j = k;
                assoc = lookup_Associa (pathmap, &xn);
                if (!assoc)  continue;
                p_ik = *(ujint*) val_of_Assoc (assoc);

                xn.i = k;
                xn.j = p.j;
                assoc = lookup_Associa (xnmap, &xn);
                Claim( assoc );
                t_kj = xns.s[*(ujint*) val_of_Assoc (assoc)].idx;

                q_ikj = fmla->nvbls ++;
                    /* We wish for (q_{ikj} == p_{ik} && t_{kj}).*/

                    /* (q_{ikj} => p_{ik}) */
                clause->lits.sz = 0;
                app_CnfDisj (clause, false, q_ikj);
                app_CnfDisj (clause, true , p_ik );
                app_CnfFmla (fmla, clause);
                    /* (q_{ikj} => t_{kj}) */
                clause->lits.sz = 0;
                app_CnfDisj (clause, false, q_ikj);
                app_CnfDisj (clause, true , t_kj );
                app_CnfFmla (fmla, clause);
                    /* (p_{ik} && t_{kj} => q_{ikj}) */
                clause->lits.sz = 0;
                app_CnfDisj (clause, true , q_ikj);
                app_CnfDisj (clause, false, p_ik );
                app_CnfDisj (clause, false, t_kj );
                app_CnfFmla (fmla, clause);
            }

                /* (q_{ikj} => p_{ij}) */
            clause->lits.sz = 0;
            app_CnfDisj (clause, false, q_ikj);
            app_CnfDisj (clause, true , p_ij );
            app_CnfFmla (fmla, clause);

            app_CnfDisj (path_clause, true, q_ikj);
        } BLose()
        app_CnfFmla (fmla, path_clause);
        lose_CnfDisj (path_clause);
    } BLose()

        /* Lose everything we can before running the solve.*/
    { BUjFor( i, states.sz )
        LoseTable( states.s[i].tx );
        LoseTable( states.s[i].to );
    } BLose()
    LoseTable( states );
    lose_Associa (pathmap);
    lose_Associa (xnmap);
    LoseTable( xns );
    lose_CnfDisj (clause);

    {
        BitTable evs = cons2_BitTable (fmla->nvbls, 0);
        bool sat = false;
        extl_solve_CnfFmla (fmla, &sat, evs);
        if (0)
        {
            dump_BitTable (stderr_OFileB (), evs);
            dump_char_OFileB (stderr_OFileB (), '\n');
        }

        tape->stabilizing = sat;
        if (sat)
        { BUjFor( i, may_rules->sz )
            if (test_BitTable (evs, i))
            {
                rule_XnSys (g, sys, may_rules->s[i]);
                add_XnRule (tape, g);
                g = grow1_rules_synsearch (tape);
            }
        } BLose()
        lose_BitTable (&evs);
    }
    -- tape->rules.sz;

    lose_CnfFmla (fmla);
}

    int
main ()
{
    const bool SystemInitialized = (init_sys_cx (), true);
    DecloStack1( XnSys, sys, dflt_XnSys () );
    DecloStack1( CnfFmla, fmla, dflt_CnfFmla () );
    BoolLit clauses[][3] = {
        {{Yes, 0}, {Yes, 1}, {Yes, 0}},
        {{Yes, 1}, {Nil, 0}, {Yes, 1}},
            /* {{Nil, 1}, {Yes, 0}, {Nil, 1}}, */
        {{Yes, 1}, {Yes, 1}, {Nil, 1}},
        {{Yes, 2}, {Yes, 1}, {Nil, 2}},
        {{Nil, 2}, {Nil, 2}, {Yes, 3}},
            /* {{Nil, 3}, {Nil, 3}, {Nil, 3}}, */
            /* {{Yes, 0}, {Nil, 0}, {Yes, 0}}, */
            /* {{Yes, 0}, {Nil, 0}, {Yes, 0}}, */
            /* {{Nil, 0}, {Nil, 0}, {Nil, 0}} */
        {{Nil, 0}, {Nil, 0}, {Nil, 0}}
    };
    const bool ring = false;
    const bool use_sat_vbl = false; /* Only applies to ring.*/
    const bool manual_soln = true;
    const bool use_synsearch_sat = true;

    { BLoop( i, ArraySz(clauses) )
        CnfDisj clause = dflt_CnfDisj ();
        { BLoop( j, 3 )
            PushTable( clause.lits, clauses[i][j] );
            if (clauses[i][j].vbl + 1 > fmla->nvbls )
                fmla->nvbls = clauses[i][j].vbl + 1;
        } BLose()
        app_CnfFmla (fmla, &clause);
        lose_CnfDisj (&clause);
    } BLose()
    DBog1( "/nvbls==%u/", fmla->nvbls );

    if (!ring)
        *sys = sat3_XnSys (fmla);
    else
        *sys = sat3_ring_XnSys (fmla, use_sat_vbl);

    testfn_detect_livelock ();

    {
        bool sat = false;
        BitTable evs = cons2_BitTable (fmla->nvbls, 0);
        FnWMem_synsearch tape = cons1_FnWMem_synsearch (sys);

        extl_solve_CnfFmla (fmla, &sat, evs);
        if (sat)
        {
            DBog1( "Should be satisfiable? %s", sat ? "YES" : "NO" );
            if (manual_soln)
            {
                if (!ring)
                    sat3_soln_XnSys (&tape.rules, evs, sys);
                else
                    sat3_ring_soln_XnSys (&tape.rules, evs, sys, fmla);

                DBog1( "Giving %u hints.", (uint)tape.rules.sz );
                tape.n_cached_rules = tape.rules.sz;
            }
        }

        if (use_synsearch_sat)
            synsearch_sat (&tape);
        else
            synsearch (&tape);

        if (tape.stabilizing)  DBog0( "Solution found! :)" );
        else                   DBog0( "No solution. :(" );

        if (tape.stabilizing)
        {
            Trit stabilizing = detect_strong_convergence (&tape);
            if (stabilizing == Yes)
                DBog0( "Protocol verified, should work." );
            else
                DBog0( "Protocol could not be verified!?" );
        }

        if (tape.stabilizing || (manual_soln && tape.rules.sz > 0))
        {
            FileB pmlf;
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
        lose_FnWMem_synsearch (&tape);
        lose_BitTable (&evs);
    }

    lose_CnfFmla (fmla);
    lose_XnSys (sys);
    if (SystemInitialized)  lose_sys_cx ();
    return 0;
}

