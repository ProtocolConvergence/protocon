

/** Set the legitimate states of a 3-SAT to AddConvergence reduction.**/
static
    void
sat3_legit_XnSys (FMem_do_XnSys* fix,
                  BitTable bt,
                  XnSys* sys,
                  TableT(CnfDisj) cnf,
                  const uint npcs,
                  const uint* x_idcs,
                  const uint* y_idcs)
{
    bool ring = (npcs != 3);
#if 0
    FildeshO* out = open_FildeshOF("/dev/stderr");
    oput_BitTable(out, sys->legit);
    putc_FildeshO(out, '\n');
#endif

#if 1
    /* Enforce identity.*/
    for (uint lo = 0; lo < npcs; ++lo) {
        const uint nsatvbls = sys->vbls.s[x_idcs[0]].domsz;

        for (uint offset = 0; offset < 2; ++offset) {
            const uint hi = (lo+1+offset) % npcs;

            wipe_BitTable (bt, 0);

            set1_BitTable (fix->fixed, x_idcs[lo]);
            set1_BitTable (fix->fixed, x_idcs[hi]);

            for (uint val = 0; val < nsatvbls; ++val) {
                fix->vals[x_idcs[lo]] = val;
                fix->vals[x_idcs[hi]] = val;
                do_XnSys (fix, bt);
            }

            set0_BitTable (fix->fixed, x_idcs[lo]);
            set0_BitTable (fix->fixed, x_idcs[hi]);

            op_BitTable (bt, BitOp_NOT1, bt);

            set1_BitTable (fix->fixed, y_idcs[lo]);
            set1_BitTable (fix->fixed, y_idcs[hi]);
            for (uint val = 0; val < 2; ++val) {
                fix->vals[y_idcs[lo]] = val;
                fix->vals[y_idcs[hi]] = val;
                do_XnSys (fix, bt);
            }
            set0_BitTable (fix->fixed, y_idcs[lo]);
            set0_BitTable (fix->fixed, y_idcs[hi]);

            op_BitTable (sys->legit, BitOp_AND, bt);
        }
    }
#endif

    /* Clauses.*/
    for (uint ci = 0; ci < cnf.sz; ++ci) {
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

        for (uint permi = 0; permi < nperms; ++permi) {
            BoolLit lits[3];

            for (uint i = 0; i < 3; ++i) {
                byte idx = perms[permi][i];
                lits[i] = cnf.s[ci].lits.s[idx];
            }

            for (uint lo = 0; lo < nwindows; ++lo) {

                wipe_BitTable (bt, 0);

                /* Get variables on the stack.*/
                for (uint i = 0; i < 3; ++i) {
                    const uint pcidx = x_idcs[(lo + i) % npcs];

                    set1_BitTable (fix->fixed, pcidx);
                    fix->vals[pcidx] = (XnDomSz) lits[i].vbl;
                }

                do_XnSys (fix, bt);
                op_BitTable (bt, BitOp_NOT1, bt);

                for (uint i = 0; i < 3; ++i) {
                    const uint pcidx = y_idcs[(lo + i) % npcs];

                    set1_BitTable (fix->fixed, pcidx);
                    fix->vals[pcidx] = lits[i].val;
                    do_XnSys (fix, bt);
                    set0_BitTable (fix->fixed, pcidx);
                }

                op_BitTable (sys->legit, BitOp_AND, bt);

                wipe_BitTable (fix->fixed, 0);
            }
        }
    }


#if 0
  oput_BitTable (out, sys->legit);
  putc_FildeshO(out, '\n');

  if (false)
    for (unsigned i = 0; i < sys->legit.sz; ++i) {
      if (test_BitTable (sys->legit, i)) {
        putc_FildeshO(out, '+');
        oput_promela_state_XnSys(out, sys, i);
        putc_FildeshO(out, '\n');
      }
      else {
        putc_FildeshO(out, '-');
        oput_promela_state_XnSys(out, sys, i);
        putc_FildeshO(out, '\n');
      }
    }

  close_FildeshO(out);
#endif
}

#include "dimacs.h"

    XnSys
inst_sat3_XnSys (const CnfFmla* fmla)
{
    uint x_idcs[3];
    uint y_idcs[3];
    uint sat_idx;
    XnSys sys[] = {DEFAULT_XnSys};
    FildeshO name[] = {DEFAULT_FildeshO};

    for (uint r = 0; r < 3; ++r) {
        XnVbl x = dflt_XnVbl ();
        XnVbl y = dflt_XnVbl ();

        PushTable( sys->pcs, dflt_XnPc () );

        x.domsz = fmla->nvbls;
        truncate_FildeshO(name);
        putc_FildeshO(name, 'x');
        print_int_FildeshO(name, (int)r);
        putc_FildeshO(name, '\0');
        assign_name_of_XnVbl(&x, name->at);
        x_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, x );

        y.domsz = 2;
        truncate_FildeshO(name);
        putc_FildeshO(name, 'y');
        print_int_FildeshO(name, (int)r);
        putc_FildeshO(name, '\0');
        assign_name_of_XnVbl(&y, name->at);
        y_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, y );
    }

    PushTable( sys->pcs, dflt_XnPc () );

    {
        XnVbl sat = dflt_XnVbl ();
        sat.domsz = 2;
        truncate_FildeshO(name);
        putstrlit_FildeshO(name, "sat");
        putc_FildeshO(name, '\0');
        assign_name_of_XnVbl(&sat, name->at);
        sat_idx = sys->vbls.sz;
        PushTable( sys->vbls, sat );
    }

    for (uint r = 0; r < 3; ++r) {
        assoc_XnSys (sys, r, x_idcs[r], May);
        assoc_XnSys (sys, r, y_idcs[r], Yes);
        assoc_XnSys (sys, r, sat_idx, May);

        assoc_XnSys (sys, 3, x_idcs[r], May);
        assoc_XnSys (sys, 3, y_idcs[r], May);
    }

    assoc_XnSys (sys, 3, sat_idx, Yes);

    accept_topology_XnSys (sys);

    {
        DeclTable( CnfDisj, clauses );
        DecloStack1( FMem_do_XnSys, fix, cons1_FMem_do_XnSys (sys) );
        BitTable bt = cons2_BitTable (sys->legit.sz, 0);

        for (uint i = 0; i < fmla->idcs.sz; ++i) {
            CnfDisj clause = dflt_CnfDisj ();
            clause_of_CnfFmla (&clause, fmla, i);
            PushTable( clauses, clause );
        }

        fix->vals[sat_idx] = 1;
        set1_BitTable (fix->fixed, sat_idx);
        do_XnSys (fix, bt);
        op_BitTable (sys->legit, BitOp_AND, bt);

        sat3_legit_XnSys (fix, bt, sys, clauses, 3, x_idcs, y_idcs);

        lose_BitTable (&bt);
        lose_FMem_do_XnSys (fix);
        for (uint i = 0; i < clauses.sz; ++i) {
            lose_CnfDisj (&clauses.s[i]);
        }
        LoseTable( clauses );
    }

    /*
    for (uint i = 0; i < sys->legit.sz; ++i) {
        if (test_BitTable (sys->legit, i))
            DBog1( "%u is true", i );
    }
    */

    close_FildeshO(name);
    return *sys;
}

    XnSys
inst_sat3_ring_XnSys (const CnfFmla* fmla, const bool use_sat)
{
    uint x_idcs[5];
    uint y_idcs[ArraySz( x_idcs )];
    uint sat_idcs[ArraySz( x_idcs )];
    const uint npcs = ArraySz( x_idcs );
    XnSys sys[] = {DEFAULT_XnSys};
    FildeshO name[] = {DEFAULT_FildeshO};

    for (uint r = 0; r < npcs; ++r) {
        PushTable( sys->pcs, dflt_XnPc () );
    }

    for (uint r = 0; r < npcs; ++r) {
        x_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, dflt_XnVbl () );
    }

    for (uint r = 0; r < npcs; ++r) {
        y_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, dflt_XnVbl () );
    }

    if (use_sat)
    for (uint r = 0; r < npcs; ++r) {
        sat_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, dflt_XnVbl () );
    }

    for (uint r = 0; r < npcs; ++r) {
        XnVbl* x = &sys->vbls.s[x_idcs[r]];
        XnVbl* y = &sys->vbls.s[y_idcs[r]];

        x->domsz = fmla->nvbls;
        y->domsz = (use_sat ? 2 : 3);

        truncate_FildeshO(name);
        putc_FildeshO(name, 'x');
        print_int_FildeshO(name, (int)r);
        putc_FildeshO(name, '\0');
        assign_name_of_XnVbl(x, name->at);

        truncate_FildeshO(name);
        putc_FildeshO(name, 'y');
        print_int_FildeshO(name, (int)r);
        putc_FildeshO(name, '\0');
        assign_name_of_XnVbl(y, name->at);


        /* Process r */
        assoc_XnSys (sys, r, x_idcs[r], May);
        assoc_XnSys (sys, r, y_idcs[r], Yes);

        /* Process r+1 */
        assoc_XnSys (sys, (r + 1) % npcs, x_idcs[r], May);
        assoc_XnSys (sys, (r + 1) % npcs, y_idcs[r], May);

        /* Process r-1 */
        assoc_XnSys (sys, (r + npcs - 1) % npcs, x_idcs[r], May);
        assoc_XnSys (sys, (r + npcs - 1) % npcs, y_idcs[r], May);
    }

    if (use_sat)
    for (unsigned r = 0; r < npcs; ++r) {
        XnVbl* sat = &sys->vbls.s[sat_idcs[r]];
        sat->domsz = 2;

        truncate_FildeshO(name);
        putstrlit_FildeshO(name, "sat");
        print_int_FildeshO(name, (int)r);
        putc_FildeshO(name, '\0');
        assign_name_of_XnVbl(sat, name->at);
        /* Process r */
        assoc_XnSys (sys, r, sat_idcs[r], Yes);
        /* Process r+1 */
        assoc_XnSys (sys, (r + 1) % npcs, sat_idcs[r], May);
        /* Process r-1 */
        assoc_XnSys (sys, (r + npcs - 1) % npcs, sat_idcs[r], May);
    }

    close_FildeshO(name);

    accept_topology_XnSys (sys);

    {
        DeclTable( CnfDisj, clauses );
        DecloStack1( FMem_do_XnSys, fix, cons1_FMem_do_XnSys (sys) );
        BitTable bt = cons2_BitTable (sys->legit.sz, 0);

        for (uint i = 0; i < fmla->idcs.sz; ++i) {
            CnfDisj clause = dflt_CnfDisj ();
            clause_of_CnfFmla (&clause, fmla, i);
            PushTable( clauses, clause );
        }

        if (use_sat)
        {
            for (uint i = 0; i < npcs; ++i) {
                fix->vals[sat_idcs[i]] = 1;
                set1_BitTable (fix->fixed, sat_idcs[i]);
            }
            do_XnSys (fix, bt);
            op_BitTable (sys->legit, BitOp_AND, bt);
        }
        else
        {
            for (uint i = 0; i < npcs; ++i) {
                set1_BitTable (fix->fixed, y_idcs[i]);
                fix->vals[y_idcs[i]] = 2;
                wipe_BitTable (bt, 0);
                do_XnSys (fix, bt);
                op_BitTable (bt, BitOp_NOT1, bt);
                op_BitTable (sys->legit, BitOp_AND, bt);
                set0_BitTable (fix->fixed, y_idcs[i]);
            }
        }

        wipe_BitTable (bt, 0);

        sat3_legit_XnSys (fix, bt, sys, clauses, npcs, x_idcs, y_idcs);

        lose_BitTable (&bt);
        lose_FMem_do_XnSys (fix);
        for (uint i = 0; i < clauses.sz; ++i) {
            lose_CnfDisj (&clauses.s[i]);
        }
        LoseTable( clauses );
    }

    return *sys;
}

/** Give a solution hint for the simple 3-SAT to AddConvergence reduction.**/
    void
sat3_soln_XnSys (TableT(XnRule)* rules,
                 const BitTable evs, const XnSys* sys)
{
    for (uint pcidx = 0; pcidx < 3; ++pcidx) {
        const XnPc* pc = &sys->pcs.s[pcidx];
        uint x_idx = 0;
        uint y_idx = 0;
        uint sat_idx = 0;
        const XnVbl* x_vbl;
        //const XnVbl* y_vbl;

        for (uint i = 0; i < 3; ++i) {
            char c = sys->vbls.s[pc->vbls.s[i]].name[0];
            if (c == 'x')  x_idx = i;
            if (c == 'y')  y_idx = i;
            if (c == 's')  sat_idx = i;
        }

        x_vbl = &sys->vbls.s[pc->vbls.s[x_idx]];
        //y_vbl = &sys->vbls.s[pc->vbls.s[y_idx]];

        for (uint x_val = 0; x_val < x_vbl->domsz; ++x_val) {
            XnRule g = cons2_XnRule (3, 1);
            Bit y_val = test_BitTable (evs, x_val);

            g.pc = pcidx;
            g.p.s[x_idx] = x_val;
            g.p.s[y_idx] = !y_val;
            g.p.s[sat_idx] = 0;
            g.q.s[y_idx] = y_val;
            PushTable( *rules, g );
        }
    }
}

/** Give a solution hint for a 3-SAT to AddConvergence ring reduction.**/
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
    for (uint pcidx = 0; pcidx < sys->pcs.sz; ++pcidx) {
        x_idcs.s[pcidx] = sys->vbls.sz;
        y_idcs.s[pcidx] = sys->vbls.sz;
        sat_idcs.s[pcidx] = sys->vbls.sz;
    }

    for (uint i = 0; i < sys->vbls.sz; ++i) {
        const XnVbl* x = &sys->vbls.s[i];
        char c = x->name[0];
        uint pcidx = 0;
        uint mid = x->pcs.s[2];
        uint min = mid;
        uint max = mid;

        Claim2( x->pcs.sz ,==, 3 );
        for (uint j = 0; j < 2; ++j) {
            uint a = x->pcs.s[j];
            if      (a < min) { mid = min; min = a; }
            else if (a > max) { mid = max; max = a; }
            else              { mid = a; }
        }
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
    }

    for (uint pcidx = 0; pcidx < sys->pcs.sz; ++pcidx) {
        Claim2( x_idcs.s[pcidx] ,<, sys->vbls.sz );
        Claim2( y_idcs.s[pcidx] ,<, sys->vbls.sz );
        if (use_sat)
            Claim2( sat_idcs.s[pcidx] ,<, sys->vbls.sz );
    }

    for (uint pcidx = 0; pcidx < sys->pcs.sz; ++pcidx) {
        const uint npcs = sys->pcs.sz;
        const uint oh_pcidx = pcidx;
        const uint hi_pcidx = (oh_pcidx + 1) % npcs;
        const uint lo_pcidx = (oh_pcidx + npcs - 1) % npcs;

        const XnPc* pc = &sys->pcs.s[pcidx];
        const XnSz n_rule_steps =
            pc->rule_stepsz_q.s[0] *
            sys->vbls.s[pc->vbls.s[0]].domsz;
        XnRule g = cons3_XnRule (pcidx, pc->vbls.sz, pc->nwvbls);
        uint x_pidcs[3];
        uint y_pidcs[3];
        uint sat_pidcs[3];
        TableT(uint) vbls;

        vbls = pc->vbls;
        if (!use_sat)  Claim2( vbls.sz ,==, 6 );
        else           Claim2( vbls.sz ,==, 9 );

        for (uint i = 0; i < 3; ++i) {
            x_pidcs[i] = vbls.sz;
            y_pidcs[i] = vbls.sz;
            sat_pidcs[i] = vbls.sz;
        }

        for (uint i = 0; i < vbls.sz; ++i) {
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
        }

        for (uint i = 0; i < 3; ++i) {
            Claim2( x_pidcs[i] ,<, vbls.sz );
            Claim2( y_pidcs[i] ,<, vbls.sz );
            if (use_sat)
                Claim2( sat_pidcs[i] ,<, vbls.sz );
        }

        for (uint rule_step_idx = 0; rule_step_idx < n_rule_steps; ++rule_step_idx) {
            const XnSz rule_step = pc->rule_step + rule_step_idx;
            bool add = false;
            Bit soln_y = test_BitTable (evs, g.p.s[x_pidcs[0]]);
            Bit lo_soln_y = test_BitTable (evs, g.p.s[x_pidcs[1]]);
            Bit hi_soln_y = test_BitTable (evs, g.p.s[x_pidcs[2]]);
            bool xy_legit = true;

            rule_XnSys (&g, sys, rule_step);

            for (uint i = 0; i < fmla->idcs.sz; ++i) {
                bool allin = true;
                bool satisfied = false;

                clause.lits.sz = 0;
                clause_of_CnfFmla (&clause, fmla, i);

                for (uint j = 0; j < 3; ++j) {
                    bool found = false;

                    for (uint k = 0; k < 3; ++k) {
                        if (g.p.s[x_pidcs[j]] == clause.lits.s[j].vbl)
                        {
                            if (g.p.s[y_pidcs[j]] == clause.lits.s[j].val)
                                satisfied = true;
                            found = true;
                        }
                    }

                    if (satisfied)  break;
                    if (!found)
                    {
                        allin = false;
                        break;
                    }
                }

                if (allin && !satisfied)
                {
                    xy_legit = false;
                    break;
                }
            }

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
        }

        lose_XnRule (&g);
    }

    LoseTable( x_idcs );
    LoseTable( y_idcs );
    LoseTable( sat_idcs );
    lose_CnfDisj (&clause);
}

