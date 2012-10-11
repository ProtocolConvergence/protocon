
    void
oput_pla_XnEVbl (OFileB* of, const XnEVbl* x)
{
    const uint n = x->vbl->domsz;
    {:for (i ; n)
        oput_char_OFileB (of, (i == (uint) x->val) ? '1' : '0');
    }
}

    void
oput_pla_state_XnSys (OFileB* of, const XnSys* sys, const ujint sidx)
{
    const Bit legit = test_BitTable (sys->legit, sidx);
    ujint idx = sidx;
    {:for (i ; sys->vbls.sz)
        XnEVbl x;
        x.vbl = &sys->vbls.s[i];
        x.val = idx / x.vbl->stepsz;
        idx = idx % x.vbl->stepsz;
        oput_char_OFileB (of, ' ');
        oput_pla_XnEVbl (of, &x);
    }
    oput_char_OFileB (of, ' ');
    oput_cstr_OFileB (of, legit ? "01" : "10");
}

    void
oput_pla_legit (OFileB* of, const XnSys* sys)
{
    oput_cstr_OFileB (of, ".mv ");
    oput_uint_OFileB (of, sys->vbls.sz + 1);
    oput_cstr_OFileB (of, " 0");
    {:for (i ; sys->vbls.sz)
        oput_char_OFileB (of, ' ');
        oput_uint_OFileB (of, sys->vbls.s[i].domsz);
    }
    oput_cstr_OFileB (of, " 2\n");
    {:for (i ; sys->nstates)
        oput_pla_state_XnSys (of, sys, i);
        oput_char_OFileB (of, '\n');
    }
    oput_cstr_OFileB (of, ".e\n");
}

    void
oput_pla_XnRule (OFileB* of, const XnRule* g, const XnSys* sys)
{
    const XnPc* pc = &sys->pcs.s[g->pc];
    {:for (i ; pc->vbls.sz)
        XnEVbl x;
        x.vbl = &sys->vbls.s[pc->vbls.s[i]];
        x.val = g->p.s[i];
        oput_char_OFileB (of, ' ');
        oput_pla_XnEVbl (of, &x);
    }
    {:for (i ; pc->nwvbls)
        XnEVbl x;
        x.vbl = &sys->vbls.s[pc->vbls.s[i]];
        x.val = g->p.s[i];
        oput_char_OFileB (of, ' ');
        oput_pla_XnEVbl (of, &x);
    }
}

    void
oput_pla_pc (OFileB* of, const XnPc* pc, const XnSys* sys,
             const TableT(XnRule) rules)
{
    const uint pcidx = IdxEltTable (sys->pcs, pc);
    oput_cstr_OFileB (of, ".mv ");
    oput_uint_OFileB (of, pc->vbls.sz + pc->nwvbls);
    oput_cstr_OFileB (of, " 0");
    {:for (i ; pc->vbls.sz)
        oput_char_OFileB (of, ' ');
        oput_uint_OFileB (of, sys->vbls.s[pc->vbls.s[i]].domsz);
    }
    {:for (i ; pc->nwvbls)
        oput_char_OFileB (of, ' ');
        oput_uint_OFileB (of, sys->vbls.s[pc->vbls.s[i]].domsz);
    }
    oput_char_OFileB (of, '\n');

    oput_char_OFileB (of, '#');
    {:for (i ; pc->vbls.sz)
        oput_char_OFileB (of, ' ');
        oput_AlphaTab (of, &sys->vbls.s[pc->vbls.s[i]].name);
    }
    {:for (i ; pc->nwvbls)
        oput_char_OFileB (of, ' ');
        oput_AlphaTab (of, &sys->vbls.s[pc->vbls.s[i]].name);
        oput_char_OFileB (of, '\'');
    }
    oput_char_OFileB (of, '\n');

    {:for (i ; rules.sz)
        const XnRule* g = &rules.s[i];
        if (g->pc == pcidx)
        {
            oput_pla_XnRule (of, g, sys);
            oput_char_OFileB (of, '\n');
        }
    }
    oput_cstr_OFileB (of, ".e\n");
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
    oput_pla_legit (of, sys);
#endif

    BInit();

    stdxpipe_OSPc (ospc);
    stdopipe_OSPc (ospc);
    ospc->cmd = cons1_AlphaTab ("espresso");
    /* Using -Dexact can take a long time.*/
    /* PushTable( ospc->args, cons1_AlphaTab ("-Dexact") ); */
    good = spawn_OSPc (ospc);
    BCasc( good, good, "spawn_OSPc()" );

    oput_pla_legit (ospc->of, sys);
    close_OFileB (ospc->of);
    xget_XFileB (ospc->xf);
    if (0)
        oput_cstr_OFileB (of, cstr1_XFileB (ospc->xf, 0));
    close_OSPc (ospc);

    if (0)
    {:for (pcidx ; sys->pcs.sz)
        good = spawn_OSPc (ospc);
        if (!good)  break;
        oput_pla_pc (ospc->of, &sys->pcs.s[pcidx], sys, rules);
        close_OFileB (ospc->of);
        oput_cstr_OFileB (of, xget_FileB (&ospc->xfb));
        close_OSPc (ospc);
    }

    BCasc( good, good, "spawn_OSPc()" );

    BLose();

    /* lose_FileB (&ofb); */
    lose_OSPc (ospc);
    return good;
}

