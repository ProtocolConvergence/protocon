

/** Set the legitimate states of a 3-SAT to AddConvergence reduction.**/
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

#include "dimacs.c"

    XnSys
inst_sat3_XnSys (const CnfFmla* fmla)
{
    uint x_idcs[3];
    uint y_idcs[3];
    uint sat_idx;
    DecloStack( XnSys, sys );
    OFileB name = dflt_OFileB ();

    *sys = dflt_XnSys ();

    { BLoop( r, 3 )
        XnVbl x = dflt_XnVbl ();
        XnVbl y = dflt_XnVbl ();

        PushTable( sys->pcs, dflt_XnPc () );

        x.max = fmla->nvbls-1;
        flush_OFileB (&name);
        printf_OFileB (&name, "x%u", r);
        copy_AlphaTab_OFileB (&x.name, &name);
        x_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, x );

        y.max = 1;
        flush_OFileB (&name);
        printf_OFileB (&name, "y%u", r);
        copy_AlphaTab_OFileB (&y.name, &name);
        y_idcs[r] = sys->vbls.sz;
        PushTable( sys->vbls, y );
    } BLose()

    PushTable( sys->pcs, dflt_XnPc () );

    {
        XnVbl sat = dflt_XnVbl ();
        sat.max = 1;
        flush_OFileB (&name);
        dump_cstr_OFileB (&name, "sat");
        copy_AlphaTab_OFileB (&sat.name, &name);
        sat_idx = sys->vbls.sz;
        PushTable( sys->vbls, sat );
    }

    { BLoop( r, 3 )
        assoc_XnSys (sys, r, x_idcs[r], May);
        assoc_XnSys (sys, r, y_idcs[r], Yes);
        assoc_XnSys (sys, r, sat_idx, May);

        assoc_XnSys (sys, 3, x_idcs[r], May);
        assoc_XnSys (sys, 3, y_idcs[r], May);
    } BLose()

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

    lose_OFileB (&name);
    return *sys;
}

    XnSys
inst_sat3_ring_XnSys (const CnfFmla* fmla, const bool use_sat)
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
        copy_AlphaTab_OFileB (&x->name, &name);

        flush_OFileB (&name);
        printf_OFileB (&name, "y%u", r);
        copy_AlphaTab_OFileB (&y->name, &name);


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
        copy_AlphaTab_OFileB (&sat->name, &name);
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

/** Give a solution hint for the simple 3-SAT to AddConvergence reduction.**/
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

