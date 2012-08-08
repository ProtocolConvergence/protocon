
    void
dump_pla_XnEVbl (OFileB* of, const XnEVbl* x)
{
    const uint n = (uint) x->vbl->max + 1;
    { BLoop( i, n )
        dump_char_OFileB (of, (i == (uint) x->val) ? '1' : '0');
    } BLose()
}

    void
dump_pla_state_XnSys (OFileB* of, const XnSys* sys, const ujint sidx)
{
    const Bit legit = test_BitTable (sys->legit, sidx);
    ujint idx = sidx;
    { BLoop( i, sys->vbls.sz )
        XnEVbl x;
        x.vbl = &sys->vbls.s[i];
        x.val = idx / x.vbl->stepsz;
        idx = idx % x.vbl->stepsz;
        dump_char_OFileB (of, ' ');
        dump_pla_XnEVbl (of, &x);
    } BLose()
    dump_char_OFileB (of, ' ');
    dump_cstr_OFileB (of, legit ? "01" : "10");
}

    void
dump_pla_legit (OFileB* of, const XnSys* sys)
{
    dump_cstr_OFileB (of, ".mv ");
    dump_uint_OFileB (of, sys->vbls.sz + 1);
    dump_cstr_OFileB (of, " 0");
    { BLoop( i, sys->vbls.sz )
        dump_char_OFileB (of, ' ');
        dump_uint_OFileB (of, (uint)sys->vbls.s[i].max + 1);
    } BLose()
    dump_cstr_OFileB (of, " 2\n");
    { BUjFor( i, sys->nstates )
        dump_pla_state_XnSys (of, sys, i);
        dump_char_OFileB (of, '\n');
    } BLose()
    dump_cstr_OFileB (of, ".e\n");
}

    void
dump_pla_XnRule (OFileB* of, const XnRule* g, const XnSys* sys)
{
    const XnPc* pc = &sys->pcs.s[g->pc];
    { BLoop( i, pc->vbls.sz )
        XnEVbl x;
        x.vbl = &sys->vbls.s[pc->vbls.s[i]];
        x.val = g->p.s[i];
        dump_char_OFileB (of, ' ');
        dump_pla_XnEVbl (of, &x);
    } BLose()
    { BLoop( i, pc->nwvbls )
        XnEVbl x;
        x.vbl = &sys->vbls.s[pc->vbls.s[i]];
        x.val = g->p.s[i];
        dump_char_OFileB (of, ' ');
        dump_pla_XnEVbl (of, &x);
    } BLose()
}

    void
dump_pla_pc (OFileB* of, const XnPc* pc, const XnSys* sys,
             const TableT(XnRule) rules)
{
    const uint pcidx = IdxEltTable (sys->pcs, pc);
    dump_cstr_OFileB (of, ".mv ");
    dump_uint_OFileB (of, pc->vbls.sz + pc->nwvbls);
    dump_cstr_OFileB (of, " 0");
    { BLoop( i, pc->vbls.sz )
        dump_char_OFileB (of, ' ');
        dump_uint_OFileB (of, sys->vbls.s[pc->vbls.s[i]].max + 1);
    } BLose()
    { BLoop( i, pc->nwvbls )
        dump_char_OFileB (of, ' ');
        dump_uint_OFileB (of, sys->vbls.s[pc->vbls.s[i]].max + 1);
    } BLose()
    dump_char_OFileB (of, '\n');

    dump_char_OFileB (of, '#');
    { BLoop( i, pc->vbls.sz )
        dump_char_OFileB (of, ' ');
        dump_AlphaTab (of, &sys->vbls.s[pc->vbls.s[i]].name);
    } BLose()
    { BLoop( i, pc->nwvbls )
        dump_char_OFileB (of, ' ');
        dump_AlphaTab (of, &sys->vbls.s[pc->vbls.s[i]].name);
        dump_char_OFileB (of, '\'');
    } BLose()
    dump_char_OFileB (of, '\n');

    { BLoopT( XnSz, i, rules.sz )
        const XnRule* g = &rules.s[i];
        if (g->pc == pcidx)
        {
            dump_pla_XnRule (of, g, sys);
            dump_char_OFileB (of, '\n');
        }
    } BLose()
    dump_cstr_OFileB (of, ".e\n");
}

    bool
do_pla_XnSys (const XnSys* sys, const TableT(XnRule) rules)
{
    bool good = true;
    DecloStack1( OSPc, ospc, dflt_OSPc () );
    OFileB* of = stdout_OFileB ();

#if 0
    FileB ofb;
    init_FileB (&ofb);
    seto_FileB (&ofb, true);
    open_FileB (&ofb, 0, "legit0.esp");
    of = &ofb.xo;
    dump_pla_legit (of, sys);
#endif

    BInit();

    stdxpipe_OSPc (ospc);
    stdopipe_OSPc (ospc);
    ospc->cmd = cons1_AlphaTab ("espresso");
    PushTable( ospc->args, cons1_AlphaTab ("-Dexact") );
    good = spawn_OSPc (ospc);
    BCasc( good, good, "spawn_OSPc()" );

    dump_pla_legit (ospc->of, sys);
    close_OFileB (ospc->of);
    load_XFileB (ospc->xf);
    if (0)
        dump_cstr_OFileB (of, cstr1_XFileB (ospc->xf, 0));
    close_OSPc (ospc);

    if (0)
    { BUjFor( pcidx, sys->pcs.sz )
        good = spawn_OSPc (ospc);
        if (!good)  break;
        dump_pla_pc (ospc->of, &sys->pcs.s[pcidx], sys, rules);
        close_OFileB (ospc->of);
        dump_cstr_OFileB (of, load_FileB (&ospc->xfb));
        close_OSPc (ospc);
    } BLose()

    BCasc( good, good, "spawn_OSPc()" );

    BLose();

    /* lose_FileB (&ofb); */
    lose_OSPc (ospc);
    return good;
}

