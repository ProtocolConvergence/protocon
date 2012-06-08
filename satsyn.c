
#include "cx/bittable.h"
#include "cx/fileb.h"
#include "cx/sys-cx.h"
#include "cx/table.h"

#include <assert.h>
#include <stdio.h>

typedef struct XnPc XnPc;
typedef struct XnVbl XnVbl;
typedef struct XnEVbl XnEVbl;
typedef struct XnSys XnSys;
typedef BitTableSz XnSz;
typedef byte DomSz;
typedef struct Disj3 Disj3;

DeclTableT( XnPc, XnPc );
DeclTableT( XnVbl, XnVbl );
DeclTableT( XnEVbl, XnEVbl );
DeclTableT( XnSz, XnSz );
DeclTableT( Disj3, Disj3 );

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

struct XnSys
{
    TableT(XnPc) pcs;
    TableT(XnVbl) vbls;
    BitTable legit;
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
dump_BitTable (FileB* f, const BitTable bt)
{
    BitTableSz i;
    UFor( i, bt.sz )
        dump_char_FileB (f, test_BitTable (bt, i) ? '1' : '0');
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

    int
iswapped_XnEVbl (const void* av, const void* bv)
{
    const XnEVbl* a = (XnEVbl*) av;
    const XnEVbl* b = (XnEVbl*) bv;
    if ((size_t) a->vbl < (size_t) b->vbl)  return -1;
    if ((size_t) a->vbl > (size_t) b->vbl)  return  1;
    return 0;
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

static
    void
recu_save_do_XnSys (BitTable* bt, TableT(XnEVbl)* p, uint i)
{
    XnEVbl x;

    if (i == p->sz)
    {
        qsort (p->s, p->sz, sizeof (*p->s), iswapped_XnEVbl);
        recu_do_XnSys (bt, p->s, p->sz, 0, bt->sz);
        return;
    }

    x = p->s[i];
    recu_save_do_XnSys (bt, p, i+1);
    p->s[i] = x;
}

    void
do_XnSys (BitTable bt, TableT(XnEVbl) p)
{
    recu_save_do_XnSys (&bt, &p, 0);
}

    void
sat3_legit_XnSys (XnSys* sys, TableT(Disj3) cnf)
{
    BitTable bt = cons1_BitTable (sys->legit.sz);
    DeclTable( XnEVbl, p );
    FileB* xf = stderr_FileB ();

    dump_BitTable (xf, sys->legit);
    dump_char_FileB (xf, '\n');

#if 1
    GrowTable( p, 2 );
    { BLoop( i, 3 )
        const uint n = 1 + (uint) sys->vbls.s[0].max;
        uint j;
        for (j = i+1; j < 3; ++j)
        {
            wipe_BitTable (bt, 0);

            p.s[0].vbl = &sys->vbls.s[2*i];
            p.s[1].vbl = &sys->vbls.s[2*j];
            { BLoop( val, n )
                p.s[0].val = p.s[1].val = val;
                do_XnSys (bt, p);
            } BLose()

            op_BitTable (bt, bt, BitTable_NOT);

            p.s[0].vbl = &sys->vbls.s[2*i+1];
            p.s[1].vbl = &sys->vbls.s[2*j+1];
            { BLoop( val, 2 )
                p.s[0].val = p.s[1].val = val;
                do_XnSys (bt, p);
            } BLose()

            op_BitTable (sys->legit, bt, BitTable_AND);
        }
    } BLose()
    p.sz = 0;
#endif

        /* Clauses.*/
    { BLoop( ci, cnf.sz )
        static const byte perms[][3] = {
#if 0
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
            p.sz = 0;

                /* Get variables on the stack.*/
            { BLoop( i, 3 )
                int v = clause.terms[i];
                XnEVbl x;

                x.vbl = &sys->vbls.s[2*i];
                x.val = (DomSz) (v > 0 ? v : -v) - 1;
                PushTable( p, x );
            } BLose()

            do_XnSys (bt, p);
            op_BitTable (bt, bt, BitTable_NOT);

            { BLoop( i, 3 )
                int v = clause.terms[i];
                XnEVbl x;

                x.vbl = &sys->vbls.s[2*i+1];
                x.val = (v > 0);

                PushTable( p, x );
                do_XnSys (bt, p);
                p.sz --;
            } BLose()

            op_BitTable (sys->legit, bt, BitTable_AND);
        } BLose()
    } BLose()

    LoseTable( p );
    lose_BitTable( &bt );

    dump_BitTable (xf, sys->legit);
    dump_char_FileB (xf, '\n');
}

    XnSys
sat3_XnSys ()
{
    Disj3 clauses[] = {
        {{ 1, 1, 1 }},
        {{ -2, -2, -2 }},
    };
    DeclTable( Disj3, cnf );
    const uint n = 2;
    DecloStack( XnSys, sys );

    *sys = dflt_XnSys ();
    cnf.s = clauses;
    cnf.sz = ArraySz( clauses );

    { BLoop( i, 3 )
        PushTable( sys->pcs, dflt_XnPc () );
    } BLose()

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
    } BLose()

    accept_topology_XnSys (sys);

    sat3_legit_XnSys (sys, cnf);

    { BLoop( i, sys->legit.sz )
        if (test_BitTable (sys->legit, i))
            DBog1( "%u is true", i );
    } BLose()
    
    return *sys;
}

    void
dump_cnf_XnSys (FileB* f, const XnSys* sys)
{
    const XnSz nstates = size_XnSys (sys);
    const XnSz nxns = nstates * nstates;
    const uint nvbls = nstates + nxns;
    uint nclauses = 0;
}

    int
main ()
{
    DecloStack( XnSys, sys );
    init_sys_cx ();
    *sys = sat3_XnSys ();

    lose_XnSys (sys);
    lose_sys_cx ();
    return 0;
}

