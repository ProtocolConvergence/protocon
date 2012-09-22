
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
    void
dump_promela_select (OFileB* of, const XnVbl* vbl)
{
    XnEVbl x;
    x.vbl = vbl;
    dump_cstr_OFileB (of, "if\n");
    { BLoop( i, vbl->domsz )
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
        if (x->domsz <= 2)
            dump_cstr_OFileB (of, "bit");
        else
            dump_cstr_OFileB (of, "byte");

        dump_char_OFileB (of, ' ');
        dump_AlphaTab (of, &x->name );
        dump_cstr_OFileB (of, ";\n");
    } BLose()

    for (uint i = 0; i < sys->pcs.sz; ++i)
        dump_promela_pc (of, &sys->pcs.s[i], sys, rules);

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
    for (ujint i = 0; i < sys->legit.sz; ++i)
    {
        if (!test_BitTable (sys->legit, i))
        {
            dump_cstr_OFileB (of, ":: ");
            dump_promela_state_XnSys (of, sys, i);
            dump_cstr_OFileB (of, " -> skip;\n");
        }
    }
    dumpl( "fi;" );
    dumpl( "Legit = false;" );
    dumpl( "assert(0);" );
    dumpl( "}" );

    dumpl( "ltl {" );
    dumpl( "<> Legit && [] (Legit -> [] Legit)" );
    dumpl( "}" );
#undef dumpl
}

