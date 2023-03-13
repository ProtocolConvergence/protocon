
#include "xnsys.h"

#include <stdio.h>

    XnVblSymm
cons2_XnVblSymm (const char* name, XnDomSz domsz)
{
    XnVblSymm x;
    x.domsz = domsz;
    x.name = cons1_AlphaTab (name);
    x.stepsz0 = 0;
    x.stepsz1 = 0;
    return x;
}
    void
lose_XnVblSymm (XnVblSymm* x)
{
    lose_AlphaTab (&x->name);
}

    XnPcSymm
cons1_XnPcSymm (const char* name)
{
    XnPcSymm pc;
    pc.name = cons1_AlphaTab (name);
    InitTable( pc.ovbls );
    InitTable( pc.xvbls );
    pc.allowed_acts = dflt_BitTable ();
    pc.defined_acts = dflt_BitTable ();
    InitTable( pc.instances );
    return pc;
}

    void
lose_XnPcSymm (XnPcSymm* pc)
{
    lose_AlphaTab (&pc->name);
    for (uint i = 0; i < pc->ovbls.sz; ++i) {
        lose_XnVblSymm (&pc->ovbls.s[i]);
    }
    for (uint i = 0; i < pc->xvbls.sz; ++i) {
        lose_XnVblSymm (&pc->xvbls.s[i]);
    }
    LoseTable( pc->ovbls );
    LoseTable( pc->xvbls );
    lose_BitTable (&pc->allowed_acts);
    lose_BitTable (&pc->defined_acts);
    LoseTable( pc->instances );
}

    void
add_vbl_XnPcSymm (XnPcSymm* pc, const char* name, XnDomSz domsz, Bit own)
{
    XnVblSymm* x;
    if (own)  x = Grow1Table( pc->ovbls );
    else      x = Grow1Table( pc->xvbls );
    *x = cons2_XnVblSymm (name, domsz);
}

/**
 * Commit to the topological properties of this symmetric process template.
 */
    void
commit_initialization_XnPcSymm (XnPcSymm* pc)
{
    XnSz stepsz = 1;
    for (uint i = 0; i < pc->xvbls.sz; ++i) {
        XnVblSymm* x = &pc->xvbls.s[pc->xvbls.sz - 1 - i];
        x->stepsz0 = stepsz;
        x->stepsz1 = 0;
        stepsz *= x->domsz;
    }
    for (uint i = 0; i < pc->ovbls.sz; ++i) {
        XnVblSymm* x = &pc->ovbls.s[pc->ovbls.sz - 1 - i];
        x->stepsz0 = stepsz;
        stepsz *= x->domsz;
    }
    pc->nstates = stepsz;
    for (uint i = 0; i < pc->ovbls.sz; ++i) {
        XnVblSymm* x = &pc->ovbls.s[pc->ovbls.sz - 1 - i];
        x->stepsz1 = stepsz;
        stepsz *= x->domsz;
    }
    pc->nactxns = stepsz;

    size_BitTable (&pc->allowed_acts, pc->nactxns);
    size_BitTable (&pc->defined_acts, pc->nactxns);
    wipe_BitTable (pc->allowed_acts, 1);
    wipe_BitTable (pc->defined_acts, 0);
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
    pc.symmetry_idx = 0;
    return pc;
}

    void
lose_XnPc (XnPc* pc)
{
    LoseTable( pc->vbls );
    LoseTable( pc->rule_stepsz_p );
    LoseTable( pc->rule_stepsz_q );
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
cons2_XnRule(unsigned np, unsigned nq)
{
  XnRule g = dflt_XnRule ();
  unsigned i;
  g.p.sz = np;
  g.q.sz = nq;
  for (i = 0; i < NMaxXnPcVbls; ++i) {
    g.p.s[i] = 0;
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
  XnSys sys = DEFAULT_XnSys;
  return sys;
}

    void
lose_XnSys (XnSys* sys)
{
    for (uint i = 0; i < sys->pcs.sz; ++i) {
        lose_XnPc (&sys->pcs.s[i]);
    }
    LoseTable( sys->pcs );
    for (uint i = 0; i < sys->vbls.sz; ++i) {
        lose_XnVbl (&sys->vbls.s[i]);
    }
    LoseTable( sys->vbls );
    lose_BitTable (&sys->legit);
    for (uint i = 0; i < sys->legit_rules.sz; ++i) {
        lose_XnRule (&sys->legit_rules.s[i]);
    }
    LoseTable( sys->legit_rules );
}

    TableT(uint)
wvbls_XnPc (const XnPc* pc)
{
    DeclTable( uint, t );
    t.s = pc->vbls.s;
    t.sz = pc->nwvbls;
    return t;
}

    TableT(uint)
rvbls_XnPc (const XnPc* pc)
{
    return pc->vbls;
}

    TableT(uint)
wpcs_XnVbl (XnVbl* x)
{
    DeclTable( uint, t );
    t.s = x->pcs.s;
    t.sz = x->nwpcs;
    return t;
}

    TableT(uint)
rpcs_XnVbl (XnVbl* x)
{
    return x->pcs;
}

    XnSz
size_XnSys (const XnSys* sys)
{
    XnSz sz = 1;

    for (uint i = 0; i < sys->vbls.sz; ++i) {
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

/** Call this when you're done specifying all processes and variables
 * and wish to start specifying invariants.
 **/
    void
accept_topology_XnSys (XnSys* sys)
{
    XnSz stepsz = 1;
    for (uint i = 0; i < sys->vbls.sz; ++i) {
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

    for (uint pcidx = 0; pcidx < sys->pcs.sz; ++pcidx) {
        XnPc* pc = &sys->pcs.s[pcidx];
        uint n;

        SizeTable( pc->rule_stepsz_p, pc->vbls.sz );
        SizeTable( pc->rule_stepsz_q, pc->nwvbls );

        stepsz = 1;

        n = pc->rule_stepsz_p.sz;
        for (uint i = 0; i < n; ++i) {
            XnSz* x = &pc->rule_stepsz_p.s[n-1-i];
            XnDomSz domsz = sys->vbls.s[pc->vbls.s[n-1-i]].domsz;

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
        for (uint i = 0; i < n; ++i) {
            XnSz* x = &pc->rule_stepsz_q.s[n-1-i];
            XnDomSz domsz = sys->vbls.s[pc->vbls.s[n-1-i]].domsz;

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
statevs_of_XnSys (TableT(XnDomSz)* t, const XnSys* sys, XnSz sidx)
{
    SizeTable( *t, sys->vbls.sz );
    for (uint i = 0; i < sys->vbls.sz; ++i) {
        const XnVbl* x = &sys->vbls.s[i];
        t->s[i] = (sidx / x->stepsz);
        sidx = (sidx % x->stepsz);
    }
}


  void
oput_XnEVbl(FildeshO* out, const XnEVbl* ev, const char* delim)
{
  puts_FildeshO(out, ccstr_of_AlphaTab(&ev->vbl->name));
  if (!delim)  delim = "=";
  puts_FildeshO(out, delim);
  print_int_FildeshO(out, (int)ev->val);
}

    void
rule_XnSys (XnRule* g, const XnSys* sys, XnSz idx)
{
    const XnPc* pc = 0;
    g->pc = sys->pcs.sz - 1;
    for (uint i = 0; i < sys->pcs.sz-1; ++i) {
        if (idx < sys->pcs.s[i+1].rule_step)
        {
            g->pc = i;
            break;
        }
    }

    pc = &sys->pcs.s[g->pc];
    idx -= pc->rule_step;

    EnsizeTable( g->q, pc->rule_stepsz_q.sz );
    for (uint i = 0; i < g->q.sz; ++i) {
        XnSz d = pc->rule_stepsz_q.s[i];
        g->q.s[i] = idx / d;
        idx = idx % d;
    }

    EnsizeTable( g->p, pc->rule_stepsz_p.sz );
    for (uint i = 0; i < g->p.sz; ++i) {
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

    for (uint i = 0; i < g->p.sz; ++i) {
        step += g->p.s[i] * pc->rule_stepsz_p.s[i];
    }
    for (uint i = 0; i < g->q.sz; ++i) {
        step += g->q.s[i] * pc->rule_stepsz_q.s[i];
    }

    return step;
}

