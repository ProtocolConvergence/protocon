/**
 * \file satsyn.c
 *
 * SAT-based stabilization synthesis.
 **/
#include "cx/syscx.h"
#include "cx/associa.h"
#include "cx/bittable.h"
#include "cx/fileb.h"
#include "cx/ospc.h"
#include "cx/table.h"

#include <assert.h>
#include <stdio.h>

#define NMaxXnPcVbls 10

enum XnSysInstance {
    Sat3Inst,
    Sat3RingInst,
    Sat3RingWSatInst,
    MatchingInst,
    ColoringInst,
    TokenRing3BitInst,
    TokenRingDijkstraInst,
    NXnSysInstances
};

typedef enum XnSysInstance XnSysInstance;

static const bool DBog_WeakChk    = true;
static const bool DBog_AssertRule = true;
static const bool DBog_SearchStep = true;
static const bool DBog_QuickTrim = false;

/** Use Z3 instead of MiniSat.**/
static const bool SatSolve_Z3 = false;

typedef struct XnPc XnPc;
typedef struct XnVbl XnVbl;
typedef struct XnEVbl XnEVbl;
typedef struct XnRule XnRule;
typedef struct XnSys XnSys;
//typedef ujint XnSz;
typedef uint XnSz;
typedef byte DomSz;
typedef struct BoolLit BoolLit;
typedef struct CnfDisj CnfDisj;
typedef struct CnfFmla CnfFmla;
typedef struct XnSz2 XnSz2;
typedef struct FMem_detect_livelock FMem_detect_livelock;
typedef struct FMem_detect_convergence FMem_detect_convergence;
typedef struct FMem_do_XnSys FMem_do_XnSys;
typedef struct FMem_synsearch FMem_synsearch;

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


/** Holds two XnSz values.**/
struct XnSz2 { XnSz i; XnSz j; };

/** Process in a transition system.**/
struct XnPc
{
    /** Variables this process uses.
     * Variables which this process can write all appear at the beginning.
     **/
    TableT(XnSz) vbls;
    /** Number of variables for which this
     * process has write and read permissions.
     **/
    XnSz nwvbls;

    XnSz nstates; /**< Same as /legit.sz/.**/

    XnSz rule_step;
    TableT(XnSz) rule_stepsz_p;
    TableT(XnSz) rule_stepsz_q;
};

/** Variable in a transition system.**/
struct XnVbl
{
    AlphaTab name;
    DomSz domsz; /**< Maximum value in the domain.**/
    TableT(XnSz) pcs; /**< List of processes which use this variable.**/
    XnSz nwpcs;  /**< Number of processes with write (and read) permission.**/
    XnSz stepsz; /**< Step size global state space.**/
};

/** Evaluation of an XnVbl.**/
struct XnEVbl
{
    DomSz val; /**< Evaluation.**/
    const XnVbl* vbl;
};

/** Transition rule (aka "action" or "transition group").**/
struct XnRule
{
    uint pc; /**< Process to which this rule belongs.**/
    FixTableT(DomSz, NMaxXnPcVbls) p; /**< Local state of the process to enable this action.**/
    FixTableT(DomSz, NMaxXnPcVbls) q; /**< New values of writable variables.**/
};

/** Transition system.**/
struct XnSys
{
    TableT(XnPc) pcs;
    TableT(XnVbl) vbls;
    BitTable legit; 
    TableT(XnRule) legit_rules;
    XnSz nstates; /**< Same as /legit.sz/.**/
    XnSz n_rule_steps;
    /** Allow new transitions in the set of legitimate states.**/
    bool syn_legit;
};

struct FMem_detect_livelock
{
    BitTable cycle;
    BitTable tested;
    TableT(XnSz2) testing;
    const BitTable* legit;
};

struct FMem_detect_convergence
{
    const BitTable* legit;
    TableT(Xns) bxns;
    TableT(XnSz) reach;
    BitTable tested;
};

struct FMem_do_XnSys
{
    DomSz* vals;
    BitTable fixed;
    TableT(XnEVbl) evs;
    const XnSys* sys;
};

struct FMem_synsearch
{
    bool stabilizing;
    const XnSys* sys;
    FMem_detect_livelock livelock_tape;
    FMem_detect_convergence convergence_tape;
    FMem_do_XnSys dostates_tape;
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

/** Boolean literal.
 * This is a variable which appears in a positive form or negated.
 **/
struct BoolLit {
    Bit  val; /**< Positive (1) or negated (0).**/
    uint vbl; /**< Index of the boolean variable.**/
};
/** Disjunction of boolean literals.**/
struct CnfDisj {
    TableT(BoolLit) lits;
};
/** Boolean formula in Conjunctive Normal Form (CNF).
 * An example CNF is:\n
 * (a || !b || c) && (!b || d) && (b || !a) && (a)
 **/
struct CnfFmla {
    uint nvbls;
    TableT(ujint) idcs;  /**< Clause indices.**/
    TableT(uint) vbls;  /**< Clause variables.**/
    BitTable vals;  /**< Clause values, negative (0) or positive (1).**/
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
add_XnRule (FMem_synsearch* tape, const XnRule* g);

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
    x.name = cons1_AlphaTab ("x");
    x.domsz = 1;
    InitTable( x.pcs );
    x.nwpcs = 0;
    x.stepsz = 0;
    return x;
}

    void
lose_XnVbl (XnVbl* x)
{
    lose_AlphaTab (&x->name);
    LoseTable( x->pcs );
}

    XnRule
dflt_XnRule ()
{
    XnRule g;
    g.pc = 0;
    InitFixTable( g.p );
    InitFixTable( g.q );
    return g;
}

    XnRule
cons2_XnRule (uint np, uint nq)
{
    XnRule g = dflt_XnRule ();
    EnsizeTable( g.p, np );
    EnsizeTable( g.q, nq );
    {:for (i ; np)
        g.p.s[i] = 0;
    }
    {:for (i ; nq)
        g.q.s[i] = 0;
    }
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
    sys.syn_legit = false;
    return sys;
}

    void
lose_XnSys (XnSys* sys)
{
    {:for (i ; sys->pcs.sz)
        lose_XnPc (&sys->pcs.s[i]);
    }
    LoseTable( sys->pcs );
    {:for (i ; sys->vbls.sz)
        lose_XnVbl (&sys->vbls.s[i]);
    }
    LoseTable( sys->vbls );
    lose_BitTable (&sys->legit);
    {:for (i ; sys->legit_rules.sz)
        lose_XnRule (&sys->legit_rules.s[i]);
    }
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
    {:for (i ; clause->lits.sz)
        BoolLit lit = clause->lits.s[i];
        if (lit.val)  set1_BitTable (fmla->vals, off+i);
        else          set0_BitTable (fmla->vals, off+i);
        fmla->vbls.s[off+i] = lit.vbl;
    }
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
oput_BitTable (OFileB* f, const BitTable bt)
{
    for (ujint i = 0; i < bt.sz; ++i)
        oput_char_OFileB (f, test_BitTable (bt, i) ? '1' : '0');
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
    return x->pcs;
}

    XnSz
size_XnSys (const XnSys* sys)
{
    XnSz sz = 1;

    {:for (i ; sys->vbls.sz)
        const XnSz psz = sz;
        sz *= (XnSz) sys->vbls.s[i].domsz;

        if (sz <= psz)
        {
            fprintf (stderr, "Size shrunk!\n");
            return 0;
        }
    }

    return sz;
}

/**
 * mode:
 * - Nil - write-only (NOT SUPPORTED)
 * - Yes - read-write
 * - May - read-only
 **/
    void
assoc_XnSys (XnSys* sys, uint pc_idx, uint vbl_idx, Trit mode)
{
    XnPc* const pc = &sys->pcs.s[pc_idx];
    XnVbl* const x = &sys->vbls.s[vbl_idx];

    Claim2( mode ,!=, Nil );

    if (mode == May)
    {
        PushTable( pc->vbls, vbl_idx );
        PushTable( x->pcs, pc_idx );
    }
    if (mode == Yes)
    {
        GrowTable( pc->vbls, 1 );
        GrowTable( x->pcs, 1 );


        for (uint i = pc->vbls.sz - 1; i > pc->nwvbls; --i)
            pc->vbls.s[i] = pc->vbls.s[i-1];
        for (uint i = x->pcs.sz - 1; i > x->nwpcs; --i)
            x->pcs.s[i] = x->pcs.s[i-1];

        pc->vbls.s[pc->nwvbls ++] = vbl_idx;
        x->pcs.s[x->nwpcs ++] = pc_idx;
    }
}

qual_inline
    uint
inc1mod (uint i, uint n)
{
    return (i + 1) % n;
}

qual_inline
    uint
dec1mod (uint i, uint n)
{
    return (i + n - 1) % n;
}

/** Call this when you're done specifying all processes and variables
 * and wish to start specifying invariants.
 **/
    void
accept_topology_XnSys (XnSys* sys)
{
    XnSz stepsz = 1;
    {:for (i ; sys->vbls.sz)
        XnVbl* x = &sys->vbls.s[sys->vbls.sz-1-i];
        x->stepsz = stepsz;
        stepsz *= x->domsz;
        if (x->domsz == 0)
        {
            DBog0( "Impossible domain size of zero." );
            failout_sysCx ("");
        }
        if (x->domsz != 1 && x->stepsz >= stepsz)
        {
            DBog0( "Cannot hold all the states!" );
            failout_sysCx ("");
        }
    }

    /* All legit states.*/
    sys->nstates = stepsz;
    sys->legit = cons2_BitTable (sys->nstates, 1);

    {:for (pcidx ; sys->pcs.sz)
        XnPc* pc = &sys->pcs.s[pcidx];
        uint n;

        SizeTable( pc->rule_stepsz_p, pc->vbls.sz );
        SizeTable( pc->rule_stepsz_q, pc->nwvbls );

        stepsz = 1;

        n = pc->rule_stepsz_p.sz;
        {:for (i ; n)
            XnSz* x = &pc->rule_stepsz_p.s[n-1-i];
            DomSz domsz = sys->vbls.s[pc->vbls.s[n-1-i]].domsz;

            *x = stepsz;
            stepsz *= domsz;
            if (domsz != 1 && *x >= stepsz)
            {
                DBog0( "Cannot hold all the rules!" );
                failout_sysCx (0);
            }
        }

        pc->nstates = stepsz;

        n = pc->rule_stepsz_q.sz;
        {:for (i ; n)
            XnSz* x = &pc->rule_stepsz_q.s[n-1-i];
            DomSz domsz = sys->vbls.s[pc->vbls.s[n-1-i]].domsz;

            *x = stepsz;
            stepsz *= domsz;
            if (domsz != 1 && *x >= stepsz)
            {
                DBog0( "Cannot hold all the rules!" );
                failout_sysCx (0);
            }
        }

        if (pcidx == 0)
            pc->rule_step = 0;

        sys->n_rule_steps = pc->rule_step + stepsz;

        if (pcidx < sys->pcs.sz-1)
            sys->pcs.s[pcidx+1].rule_step = sys->n_rule_steps;
    }
}


/** Given a state index, find the corresponding variable assignments.
 **/
    void
statevs_of_XnSys (TableT(DomSz)* t, const XnSys* sys, XnSz sidx)
{
    SizeTable( *t, sys->vbls.sz );
    {:for (i ; sys->vbls.sz)
        const XnVbl* x = &sys->vbls.s[i];
        t->s[i] = (sidx / x->stepsz);
        sidx = (sidx % x->stepsz);
    }
}


    void
oput_XnEVbl (OFileB* of, const XnEVbl* ev, const char* delim)
{
    oput_AlphaTab (of, &ev->vbl->name);
    if (!delim)  delim = "=";
    oput_cstr_OFileB (of, delim);
    oput_uint_OFileB (of, ev->val);
}

    void
rule_XnSys (XnRule* g, const XnSys* sys, XnSz idx)
{
    const XnPc* pc = 0;
    g->pc = sys->pcs.sz - 1;
    {:for (i ; sys->pcs.sz-1)
        if (idx < sys->pcs.s[i+1].rule_step)
        {
            g->pc = i;
            break;
        }
    }

    pc = &sys->pcs.s[g->pc];
    idx -= pc->rule_step;

    EnsizeTable( g->q, pc->rule_stepsz_q.sz );
    {:for (i ; g->q.sz)
        XnSz d = pc->rule_stepsz_q.s[i];
        g->q.s[i] = idx / d;
        idx = idx % d;
    }

    EnsizeTable( g->p, pc->rule_stepsz_p.sz );
    {:for (i ; g->p.sz)
        XnSz d = pc->rule_stepsz_p.s[i];
        g->p.s[i] = idx / d;
        idx = idx % d;
    }
}

    XnSz
step_XnRule (const XnRule* g, const XnSys* sys)
{
    const XnPc* pc = &sys->pcs.s[g->pc];
    XnSz step = pc->rule_step;

    {:for (i ; g->p.sz)
        step += g->p.s[i] * pc->rule_stepsz_p.s[i];
    }
    {:for (i ; g->q.sz)
        step += g->q.s[i] * pc->rule_stepsz_q.s[i];
    }

    return step;
}

#include "promela.c"


    FMem_do_XnSys
cons1_FMem_do_XnSys (const XnSys* sys)
{
    FMem_do_XnSys tape;
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
lose_FMem_do_XnSys (FMem_do_XnSys* tape)
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
    bigstepsz = stepsz * a[0].vbl->domsz;
    step += stepsz * a[0].val;

    for (; step < bel; step += bigstepsz)
        recu_do_XnSys (bt, a+1, n-1, step, step + stepsz);
}

    void
do_XnSys (FMem_do_XnSys* tape, BitTable bt)
{
    tape->evs.sz = 0;
    {:for (i ; tape->fixed.sz)
        XnEVbl e;
        if (test_BitTable (tape->fixed, i))
        {
            e.val = tape->vals[i];
            e.vbl = &tape->sys->vbls.s[i];
            PushTable( tape->evs, e );
        }
    }

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
    bigstepsz = stepsz * a[0].vbl->domsz;
    step += stepsz * a[0].val;

    for (; step < bel; step += bigstepsz)
        recu_do_push_XnSys (t, a+1, n-1, step, step + stepsz);
}

    void
do_push_XnSys (FMem_do_XnSys* tape, TableT(XnSz)* t)
{
    tape->evs.sz = 0;
    {:for (i ; tape->fixed.sz)
        XnEVbl e;
        if (test_BitTable (tape->fixed, i))
        {
            e.val = tape->vals[i];
            e.vbl = &tape->sys->vbls.s[i];
            PushTable( tape->evs, e );
        }
    }

    recu_do_push_XnSys (t, tape->evs.s, tape->evs.sz, 0, tape->sys->legit.sz);
}

    FMem_detect_livelock
cons1_FMem_detect_livelock (const BitTable* legit)
{
    FMem_detect_livelock tape;

    tape.legit = legit;

    tape.cycle = cons1_BitTable (legit->sz);
    tape.tested = cons1_BitTable (legit->sz);
    InitTable( tape.testing );
    return tape;
}

    void
lose_FMem_detect_livelock (FMem_detect_livelock* tape)
{
    lose_BitTable (&tape->cycle);
    lose_BitTable (&tape->tested);
    LoseTable( tape->testing );
}

/**
 * Detect a livelock in the current set of transition rules.
 * This is just a cycle check.
 **/
static
    bool
detect_livelock (FMem_detect_livelock* tape,
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

    FMem_detect_convergence
cons1_FMem_detect_convergence (const BitTable* legit)
{
    XnSz n = legit->sz;
    FMem_detect_convergence tape;

    tape.legit = legit;

    InitTable( tape.bxns );
    EnsizeTable( tape.bxns, n );
    {:for (i ; n)
        InitTable( tape.bxns.s[i] );
    }

    InitTable( tape.reach );
    tape.tested = cons1_BitTable (n);
    return tape;
}

    void
lose_FMem_detect_convergence (FMem_detect_convergence* tape)
{
    {:for (i ; tape->bxns.sz)
        LoseTable( tape->bxns.s[i] );
    }
    LoseTable( tape->bxns );

    LoseTable( tape->reach );
    lose_BitTable (&tape->tested);
}

/**
 * Check to see that, for any state, there exists a path to a legit state.
 * Assume the set of legit states is closed under all transitions.
 **/
    bool
detect_convergence (FMem_detect_convergence* tape,
                    const TableT(Xns) xns)
{
    TableT(Xns) bxns = tape->bxns;
    TableT(XnSz) reach = tape->reach;
    BitTable tested = tape->tested;
    XnSz nreached = 0;

    {:for (i ; bxns.sz)
        bxns.s[i].sz = 0;
    }
    reach.sz = 0;

    op_BitTable (tested, *tape->legit, BitOp_IDEN);

    {:for (i ; xns.sz)
        if (test_BitTable (tested, i))
        {
            ++ nreached;
            PushTable( reach, i );
        }

        {:for (j ; xns.s[i].sz)
            PushTable( bxns.s[xns.s[i].s[j]], i );
        }
    }

    while (reach.sz > 0)
    {
        XnSz i = *TopTable( reach );
        -- reach.sz;
        {:for (j ; bxns.s[i].sz)
            XnSz k = bxns.s[i].s[j];
            if (!set1_BitTable (tested, k))
            {
                ++ nreached;
                PushTable( reach, k );
            }
        }
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
detect_strong_convergence (FMem_synsearch* tape)
{
    if (detect_livelock (&tape->livelock_tape, tape->xns))  return Nil;

    {:for (i ; tape->xns.sz)
        if (tape->xns.s[i].sz == 0)
            if (!test_BitTable (tape->sys->legit, i))
                return May;
    }

    if (!tape->sys->syn_legit)
    {:for (i ; tape->legit_states.sz)
        XnSz s0 = tape->legit_states.s[i];
        if (tape->xns.s[s0].sz != tape->legit_xns.s[i].sz)
            return May;
    }

    return Yes;
}

    void
back1_Xn (TableT(Xns)* xns, TableT(XnSz)* stk)
{
    ujint n = *TopTable(*stk);
    ujint off = stk->sz - (n + 1);

    {:for (i ; n)
        xns->s[stk->s[off + i]].sz -= 1;
    }

    stk->sz = off;
}

    FMem_synsearch
cons1_FMem_synsearch (const XnSys* sys)
{
    FMem_synsearch tape;

    tape.stabilizing = false;
    tape.sys = sys;
    tape.livelock_tape = cons1_FMem_detect_livelock (&sys->legit);
    tape.convergence_tape = cons1_FMem_detect_convergence (&sys->legit);
    tape.dostates_tape = cons1_FMem_do_XnSys (sys);

    InitTable( tape.xns );
    GrowTable( tape.xns, sys->legit.sz );
    {:for (i ; tape.xns.sz)
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
    {:for (i ; sys->pcs.sz)
        uint nwvbls = sys->pcs.s[i].nwvbls;
        uint nrvbls = sys->pcs.s[i].vbls.sz;
        if (nwvbls > tape.rule_nwvbls)  tape.rule_nwvbls = nwvbls;
        if (nrvbls > tape.rule_nrvbls)  tape.rule_nrvbls = nrvbls;
    }

    InitTable( tape.legit_states );
    {:for (i ; sys->legit.sz)
        if (test_BitTable (sys->legit, i))
            PushTable( tape.legit_states, i );
    }

    {:for (i ; sys->legit_rules.sz)
        add_XnRule (&tape, &sys->legit_rules.s[i]);
    }

    InitTable( tape.legit_xns );
    EnsizeTable( tape.legit_xns, tape.legit_states.sz );
    {:for (i ; tape.legit_states.sz)
        InitTable( tape.legit_xns.s[i] );
        CopyTable( tape.legit_xns.s[i], tape.xns.s[tape.legit_states.s[i]] );
    }

    {:for (i ; sys->legit_rules.sz)
        back1_Xn (&tape.xns, &tape.xn_stk);
    }

    return tape;
}

    void
lose_FMem_synsearch (FMem_synsearch* tape)
{
    lose_FMem_detect_livelock (&tape->livelock_tape);
    lose_FMem_detect_convergence (&tape->convergence_tape);
    lose_FMem_do_XnSys (&tape->dostates_tape);

    {:for (i ; tape->xns.sz)
        LoseTable( tape->xns.s[i] );
    }
    LoseTable( tape->xns );
    LoseTable( tape->xn_stk );

    {:for (i ; tape->n_cached_rules)
        LoseTable( tape->rules.s[i].p );
        LoseTable( tape->rules.s[i].q );
    }
    LoseTable( tape->rules );

    {:for (i ; tape->n_cached_may_rules)
        LoseTable( tape->may_rules.s[i] );
    }
    LoseTable( tape->may_rules );

    LoseTable( tape->cmp_xn_stk );

    LoseTable( tape->influence_order );

    LoseTable( tape->legit_states );

    {:for (i ; tape->legit_xns.sz)
        LoseTable( tape->legit_xns.s[i] );
    }
    LoseTable( tape->legit_xns );
}

#define AppDelta( a, s0, s1 )  ((a) + (s1) - (s0))

    XnSz
apply1_XnRule (const XnRule* g, const XnSys* sys, XnSz sidx)
{
    const XnPc* pc = &sys->pcs.s[g->pc];
    {:for (i ; g->q.sz)
        XnSz stepsz = sys->vbls.s[pc->vbls.s[i]].stepsz;
        sidx = AppDelta( sidx,
                         stepsz * g->p.s[i],
                         stepsz * g->q.s[i] );
    }
    return sidx;
}

    void
add_XnRule (FMem_synsearch* tape, const XnRule* g)
{
    TableT(Xns)* xns = &tape->xns;
    TableT(XnSz)* stk = &tape->xn_stk;
    XnSz nadds = 0;
    XnSz sa, sb;
    DeclTable( XnSz, t );
    FMem_do_XnSys* fix = &tape->dostates_tape;

    nadds = stk->sz;

    {:for (i ; g->p.sz)
        const XnPc* pc = &tape->sys->pcs.s[g->pc];
        uint vi = pc->vbls.s[i];
        fix->vals[vi] = g->p.s[i];
        set1_BitTable (fix->fixed, vi);
    }

    do_push_XnSys (fix, stk);

    {:for (i ; g->p.sz)
        const XnPc* pc = &tape->sys->pcs.s[g->pc];
        uint vi = pc->vbls.s[i];
        set0_BitTable (fix->fixed, vi);
    }

    /* Overlay the table.*/
    t.s = &stk->s[nadds];
    t.sz = stk->sz - nadds;
    stk->sz = nadds;
    nadds = 0;

    Claim2( t.sz ,>, 0 );
    sa = t.s[0];
    sb = apply1_XnRule (g, tape->sys, sa);

    {:for (i ; t.sz)
        bool add = true;
        XnSz s0 = t.s[i];
        XnSz s1 = AppDelta( s0, sa, sb );
        /* XnSz s1 = apply1_XnRule (g, tape->sys, s0); */
        TableT(XnSz)* src = &xns->s[s0];
        Claim2( s0 ,<, tape->sys->nstates );
        Claim2( s1 ,<, tape->sys->nstates );

        {:for (j ; src->sz)
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
cmp_XnSz (const void* pa, const void* pb)
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
cmp_XnSz2 (const void* pa, const void* pb)
{
    return cmp_XnSz (&((XnSz2*)pa)->i, &((XnSz2*)pb)->i);
}
#endif

/**
 * Find the initial set of potential transition rules (actions).
 *
 * The procedure is:
 * - Ensure the existing protocol is closed.
 * - Add rules which have already been given.
 * - Add rules which do not include legitimate states in the source states.
 *   Unless either...
 *  - All legitimate source states are mapped to legitimate destination states
 *    in the legitimate protocol.
 *  - /syn_legit==true/ and all legitimate source states are mapped to
 *    legitimate destination states.
 **/
static
    void
set_may_rules (FMem_synsearch* tape, TableT(XnSz)* may_rules, XnRule* g)
{
    const XnSys* restrict sys = tape->sys;

    /* Ensure protocol is closed.*/
    {:for (i ; tape->legit_xns.sz)
        const TableT(XnSz)* t = &tape->legit_xns.s[i];
        {:for (j ; t->sz)
            if (!test_BitTable (sys->legit, t->s[j]))
            {
                DBog0( "Protocol breaks closure." );
                may_rules->sz = 0;
                return;
            }
        }
    }

    /* Note: Scrap variable /g/ is the most recent rule.*/
    /* Add preexisting rules.*/
    {:for (i ; tape->rules.sz - 1)
        add_XnRule (tape, &tape->rules.s[i]);
        if (0 == *TopTable( tape->xn_stk ))
        {
            DBog0( "Redundant rule given!" );
            back1_Xn (&tape->xns, &tape->xn_stk);
        }
    }


    {:for (i ; sys->n_rule_steps)
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
        {:for (j ; t.sz)
            const XnSz s0 = t.s[j];
            const XnSz s1 = *TopTable( tape->xns.s[s0] );

            if (!test_BitTable (sys->legit, s0))
            {
                /* Ok, start state is illegitimate.*/
            }
            else if (sys->syn_legit)
            {
                if (!test_BitTable (sys->legit, s1))
                    add = false;
            }
            else
                /* Do not add rules which cause
                 * bad transitions from legit states.
                 */
            {
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
                    add = false;
            }
            if (!add)  break;
        }

        if (add && test_selfloop)
        {
            const XnSz s0 = t.s[0];
            add = (s0 != tape->xns.s[s0].s[0]);
        }

        back1_Xn (&tape->xns, &tape->xn_stk);

        if (add)
            PushTable( *may_rules, rule_step );
    }
}

static
    XnRule*
grow1_rules_synsearch (FMem_synsearch* tape)
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
grow1_may_rules_synsearch (FMem_synsearch* tape)
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
synsearch_quicktrim_mayrules (FMem_synsearch* tape, XnSz nadded)
{
    const XnSys* sys = tape->sys;
    TableT(XnSz)* may_rules = TopTable( tape->may_rules );
    XnSz off = 0;
    XnRule* g0 = TopTable( tape->rules );

    {:for (i ; may_rules->sz)
        XnSz rule_step = may_rules->s[i];
        bool add = true;

        rule_XnSys (g0, sys, rule_step);

        Claim2( nadded+1 ,<=, tape->rules.sz );

        if (add)
        {:for (j ; nadded)
            XnRule* g1 = &tape->rules.s[tape->rules.sz-1-nadded+j];
            bool match = (g0->pc == g1->pc);

            if (match)
            {:for (k ; g0->p.sz - g0->q.sz)
                match = (g0->p.s[k+g0->q.sz] == g1->p.s[k+g0->q.sz]);
                if (!match)  break;
            }

            if (match)
            {
                /* Can't have two actions with the same guard.*/
                match = true;
                {:for (k ; g0->q.sz)
                    match = (g0->q.s[k] == g1->p.s[k]);
                    if (!match)  break;
                }
                add = !match;
                if (!add)  break;

                /* Remove actions which would not be self-disabling.*/
                match = true;
                {:for (k ; g0->q.sz)
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
            OFileB* of = stderr_OFileB ();
            oput_cstr_OFileB (of, "Pruned: ");
            oput_promela_XnRule (of, g0, sys);
            oput_char_OFileB (of, '\n');
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
synsearch_trim (FMem_synsearch* tape)
{
    const XnSys* sys = tape->sys;
    TableT(XnSz)* may_rules = TopTable( tape->may_rules );
    XnRule* g = TopTable( tape->rules );

    /* Trim down the next possible steps.*/
    if (true)
    {
        XnSz off = 0;

        {:for (i ; may_rules->sz)
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

                {:for (j ; t.sz)
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
                OFileB* of = stderr_OFileB ();
                oput_cstr_OFileB (of, "Pruned: ");
                oput_promela_XnRule (of, g, sys);
                oput_char_OFileB (of, '\n');
            }

            back1_Xn (&tape->xns, &tape->xn_stk);
        }
        may_rules->sz = off;
    }

    {
        qsort (tape->influence_order.s,
               tape->influence_order.sz,
               sizeof(*tape->influence_order.s),
               cmp_XnSz2);
        {:for (i ; tape->influence_order.sz)
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
        {:for (i ; may_rules->sz)
            XnSz rule_step = may_rules->s[i];
            rule_XnSys (g, sys, rule_step);
            add_XnRule (tape, g);
        }

        weak = detect_convergence (&tape->convergence_tape, tape->xns);

        if (!tape->sys->syn_legit)
        {:for (i ; tape->legit_states.sz)
            XnSz nout = tape->xns.s[tape->legit_states.s[i]].sz;
            if (nout != tape->legit_xns.s[i].sz)
                weak = false;
        }

        if (weak)
        {
            XnSz idx = tape->xn_stk.sz;
            tape->cmp_xn_stk.sz = 0;

            {:for (i ; may_rules->sz)
                const XnSz n = tape->xn_stk.s[idx - 1];
                idx -= n + 1;
                {:for (j ; n + 1)
                    PushTable( tape->cmp_xn_stk, tape->xn_stk.s[idx+j] );
                }
            }
        }

        {:for (i ; may_rules->sz)
            back1_Xn (&tape->xns, &tape->xn_stk);
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

    /* Find rules which are necessary.*/
    if (true)
    {
        XnSz off = 0;
        XnSz stk_idx, cmp_stk_idx;

        /* Add all rules backwards, to find which are absolutely required.*/
        {:for (i ; may_rules->sz)
            XnSz rule_step = may_rules->s[may_rules->sz - 1 - i];
            rule_XnSys (g, sys, rule_step);
            add_XnRule (tape, g);
        }

        stk_idx = tape->xn_stk.sz;
        cmp_stk_idx = tape->cmp_xn_stk.sz;

        {:for (i ; may_rules->sz)
            bool required = false;
            const XnSz nas = tape->xn_stk.s[stk_idx-1];
            const XnSz nbs = tape->cmp_xn_stk.s[cmp_stk_idx-1];
            const XnSz* as;
            const XnSz* bs;

            stk_idx -= nas + 1;
            cmp_stk_idx -= nbs + 1;

            as = &tape->xn_stk.s[stk_idx];
            bs = &tape->cmp_xn_stk.s[cmp_stk_idx];

            {:for (j ; nas)
                const XnSz s0 = as[j];
                {:for (k ; nbs)
                    if (s0 == bs[k] &&
                        tape->xns.s[s0].sz == 1 &&
                        !(sys->syn_legit && test_BitTable (sys->legit, s0)))
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
                rule_XnSys (g, sys, may_rules->s[i]);
                g = grow1_rules_synsearch (tape);
                ++ nreqrules;
            }
            else
            {
                may_rules->s[off] = may_rules->s[i];
                ++ off;
            }
        }

        {:for (i ; may_rules->sz)
            back1_Xn (&tape->xns, &tape->xn_stk);
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
synsearch (FMem_synsearch* tape)
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
            {:for (i ; nreqrules)
                add_XnRule (tape, g + i);
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
                g = grow1_rules_synsearch (tape);
                synsearch_quicktrim_mayrules (tape, nreqrules);
                -- tape->rules.sz;
                g = TopTable( tape->rules );
                synsearch (tape);
                if (tape->stabilizing)  return;
            }

            {:for (i ; nreqrules)
                back1_Xn (&tape->xns, &tape->xn_stk);
            }
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
                oput_cstr_OFileB (of, " -- ");
                oput_uint_OFileB (of, tape->may_rules.sz - 1);
                oput_cstr_OFileB (of, " -- ");
                oput_uint_OFileB (of, may_rules->sz);
                oput_cstr_OFileB (of, " -- ");
                oput_promela_XnRule (of, g, sys);
                oput_char_OFileB (of, '\n');
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


/** \test
 * Test that detect_livelock() works.
 * \sa detect_livelock()
 **/
    void
testfn_detect_livelock ()
{
    BitTable legit = cons2_BitTable (6, 0);
    DeclTable( Xns, xns );
    FMem_detect_livelock mem_detect_livelock;
    bool livelock_exists;

    GrowTable( xns, legit.sz );
    {:for (i ; xns.sz)
        InitTable( xns.s[i] );
    }

    mem_detect_livelock = cons1_FMem_detect_livelock (&legit);


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

    lose_FMem_detect_livelock (&mem_detect_livelock);

    {:for (i ; xns.sz)
        LoseTable( xns.s[i] );
    }
    LoseTable( xns );
    lose_BitTable (&legit);
}

#include "inst-sat3.c"
#include "inst-matching.c"
#include "inst-coloring.c"
#include "inst-bit3.c"
#include "inst-dijkstra.c"

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
synsearch_sat (FMem_synsearch* tape)
{
    DeclTableT( XnInfo, struct { ujint idx; CnfDisj impl; } );
    DeclTableT( State, struct { TableT(XnSz) tx; TableT(XnSz) to; } );

    DeclAssocia( XnSz, TableT(ujint), lstate_map, (SwappedFn) swapped_XnSz );
    DeclAssocia( XnSz2, ujint, xnmap, (SwappedFn) swapped_XnSz2 );
    DeclAssocia( XnSz2, ujint, pathmap, (SwappedFn) swapped_XnSz2 );

    DeclTable( State, states );
    DecloStack1( CnfFmla, fmla, dflt_CnfFmla () );
    DeclTable( XnInfo, xns );
    DecloStack1( CnfDisj, clause, dflt_CnfDisj () );

    const XnSys* restrict sys = tape->sys;
    XnRule* g;
    TableT(XnSz)* may_rules;
    Assoc* assoc;


    g = grow1_rules_synsearch (tape);
    may_rules = grow1_may_rules_synsearch (tape);

    may_rules->sz = 0;

    if (all_BitTable (sys->legit))
    {
        tape->stabilizing = true;
        CopyTable( tape->rules, sys->legit_rules );
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

    {:for (i ; tape->rules.sz-1)
        XnSz step = step_XnRule (&tape->rules.s[i], sys);
        PushTable( *may_rules, step );
    }
    tape->rules.sz = 1;
    g = &tape->rules.s[0];

    while (tape->xn_stk.sz > 0)
        back1_Xn (&tape->xns, &tape->xn_stk);

    AffyTable( states, sys->nstates );
    states.sz = sys->nstates;
    {:for (i ; states.sz)
        InitTable( states.s[i].to );
        InitTable( states.s[i].tx );
    }

    fmla->nvbls = may_rules->sz;
    {:for (i ; may_rules->sz)
        rule_XnSys (g, sys, may_rules->s[i]);
        add_XnRule (tape, g);
        {:for (j ; *TopTable(tape->xn_stk))
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
        }
        back1_Xn (&tape->xns, &tape->xn_stk);
        
        {:for (qi ; g->q.sz)
            g->q.s[qi] = 0;
        }

        {
            XnSz step = step_XnRule (g, sys);
            bool added = false;
            Assoc* assoc = ensure1_Associa (lstate_map, &step, &added);
            TableT(ujint)* rules = (TableT(ujint)*) val_of_Assoc (assoc);
            if (added)  InitTable( *rules );
            PushTable( *rules, i );
        }
    }

    {:for (i ; xns.sz)
        CnfDisj* clause = &xns.s[i].impl;
        app_CnfFmla (fmla, clause);
        lose_CnfDisj (clause);
    }

    for (assoc = beg_Associa (lstate_map);
         assoc;
         assoc = next_Assoc (assoc))
    {
        TableT(ujint)* rules = val_of_Assoc (assoc);
        {:for (i ; rules->sz)
            {:for (j ; i)
                clause->lits.sz = 0;
                app_CnfDisj (clause, false, rules->s[i]);
                app_CnfDisj (clause, false, rules->s[j]);
                app_CnfFmla (fmla, clause);
            }
        }
        LoseTable( *rules );
    }
    lose_Associa (lstate_map);

    {:for (i ; states.sz)
        if (!test_BitTable (sys->legit, i))
        {
            TableElT(State)* state = &states.s[i];

            if (state->to.sz == 0)
                DBog0( "Illegit state without outgoing transitions!!!!" );

            /* Deadlock freedom clause.*/
            clause->lits.sz = 0;
            {:for (j ; state->to.sz)
                XnSz2 t;
                Assoc* assoc;
                ujint idx;
                t.i = i;
                t.j = state->to.s[j];
                assoc = lookup_Associa (xnmap, &t);
                Claim( assoc );
                idx = xns.s[*(ujint*) val_of_Assoc (assoc)].idx;
                app_CnfDisj (clause, true, idx);
            }

            app_CnfFmla (fmla, clause);
        }

        {:for (j ; states.sz)
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
        }
    }

    for (assoc = beg_Associa (pathmap);
         assoc;
         assoc = next_Assoc (assoc))
    {
        DecloStack1( CnfDisj, path_clause, dflt_CnfDisj () );

        XnSz2 p = *(XnSz2*) key_of_Assoc (assoc);
        ujint p_ij = *(ujint*) val_of_Assoc (assoc);
        TableElT(State) state = states.s[p.j];

        app_CnfDisj (path_clause, false, p_ij);

        {:for (k_idx ; state.tx.sz)
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
        }
        app_CnfFmla (fmla, path_clause);
        lose_CnfDisj (path_clause);
    }

    /* Lose everything we can before running the solve.*/
    {:for (i ; states.sz)
        LoseTable( states.s[i].tx );
        LoseTable( states.s[i].to );
    }
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
            oput_BitTable (stderr_OFileB (), evs);
            oput_char_OFileB (stderr_OFileB (), '\n');
        }

        tape->stabilizing = sat;
        if (sat)
        {:for (i ; may_rules->sz)
            if (test_BitTable (evs, i))
            {
                rule_XnSys (g, sys, may_rules->s[i]);
                add_XnRule (tape, g);
                g = grow1_rules_synsearch (tape);
            }
        }
        lose_BitTable (&evs);
    }
    -- tape->rules.sz;

    lose_CnfFmla (fmla);
}

#include "pla.c"

    int
main (int argc, char** argv)
{
    int argi = (init_sysCx (&argc, &argv), 1);
    const XnSysInstance inst_kind =
        Sat3Inst
        /* Sat3RingInst */
        /* Sat3RingWSatInst */
        /* MatchingInst */
        /* ColoringInst */
        /* TokenRing3BitInst */
        /* TokenRingDijkstraInst */
        ;
    const bool use_synsearch_sat = true;
    const uint n_ring_pcs = 4;  /* For rings (excluding 3-SAT rings).*/
    const uint domsz = 3;
    const bool manual_soln = true;
    DecloStack1( XnSys, sys, dflt_XnSys () );
    DecloStack1( CnfFmla, fmla, dflt_CnfFmla () );
    BoolLit clauses[][3] = {
#if 0
#elif 1
        {{Yes, 0}, {Yes, 1}, {Yes, 0}},
        {{Yes, 1}, {Nil, 0}, {Yes, 1}},
        {{Yes, 1}, {Yes, 1}, {Nil, 1}},
        {{Yes, 2}, {Yes, 1}, {Nil, 2}},
        {{Nil, 2}, {Nil, 2}, {Yes, 3}},
        {{Nil, 0}, {Nil, 0}, {Nil, 0}}
#elif 0
        {{Nil, 0}, {Nil, 0}, {Nil, 0}}
#elif 0
        {{Yes, 1}, {Nil, 1}, {Yes, 0}},
        {{Nil, 0}, {Nil, 0}, {Nil, 0}}
#elif 0
        /* No solution, but not super trivial.*/
        {{Yes, 1}, {Yes, 1}, {Yes, 1}},
        {{Nil, 0}, {Nil, 0}, {Nil, 0}},
        {{Yes, 0}, {Nil, 1}, {Nil, 1}}
#endif
    };

    if (argi < argc)
        failout_sysCx ("No arguments expected.");

    {:for (i ; ArraySz(clauses))
        CnfDisj clause = dflt_CnfDisj ();
        {:for (j ; 3)
            PushTable( clause.lits, clauses[i][j] );
            if (clauses[i][j].vbl + 1 > fmla->nvbls )
                fmla->nvbls = clauses[i][j].vbl + 1;
        }
        app_CnfFmla (fmla, &clause);
        lose_CnfDisj (&clause);
    }
    DBog1( "/nvbls==%u/", fmla->nvbls );


    switch (inst_kind)
    {
    case Sat3Inst:
        *sys = inst_sat3_XnSys (fmla);
        break;
    case Sat3RingInst:
        *sys = inst_sat3_ring_XnSys (fmla, false);
        break;
    case Sat3RingWSatInst:
        *sys = inst_sat3_ring_XnSys (fmla, true);
        break;
    case MatchingInst:
        *sys = inst_matching_XnSys (n_ring_pcs);
        break;
    case ColoringInst:
        *sys = inst_coloring_XnSys (n_ring_pcs, domsz);
        break;
    case TokenRing3BitInst:
        *sys = inst_bit3_XnSys (n_ring_pcs);
        break;
    case TokenRingDijkstraInst:
        *sys = inst_dijkstra_XnSys (n_ring_pcs);
        break;
    default:
        failout_sysCx ("Invalid problem instance.");
        break;
    };

    DBog1( "size is %u", (uint) sys->nstates );

    testfn_detect_livelock ();

    {
        FMem_synsearch tape = cons1_FMem_synsearch (sys);
        if (inst_kind == Sat3Inst ||
            inst_kind == Sat3RingInst ||
            inst_kind == Sat3RingWSatInst)
        {
            bool sat = false;
            BitTable evs = cons2_BitTable (fmla->nvbls, 0);

            extl_solve_CnfFmla (fmla, &sat, evs);
            if (sat)
            {
                DBog1( "Should be satisfiable? %s", sat ? "YES" : "NO" );
                if (manual_soln)
                {
                    if (inst_kind == Sat3Inst)
                        sat3_soln_XnSys (&tape.rules, evs, sys);
                    else if (inst_kind == Sat3RingInst)
                        sat3_ring_soln_XnSys (&tape.rules, evs, sys, fmla);

                    DBog1( "Giving %u hints.", (uint)tape.rules.sz );
                    tape.n_cached_rules = tape.rules.sz;
                }
            }
            lose_BitTable (&evs);
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
            /* Promela.*/
            FileB pmlf = dflt_FileB ();

            seto_FileB (&pmlf, true);
            open_FileB (&pmlf, 0, "model.pml");
            oput_promela (&pmlf.xo, sys, tape.rules);
            lose_FileB (&pmlf);


            /* This is just a test, but should be used to
             * minimize the representation for transition rules.
             */
            do_pla_XnSys (sys, tape.rules);
        }

        lose_FMem_synsearch (&tape);
    }

    lose_CnfFmla (fmla);
    lose_XnSys (sys);
    lose_sysCx ();
    return 0;
}

