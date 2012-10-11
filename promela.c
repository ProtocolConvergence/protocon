
    void
oput_promela_state_XnSys (OFileB* of, const XnSys* sys, XnSz sidx)
{
    {:for (i ; sys->vbls.sz)
        XnEVbl x;
        x.vbl = &sys->vbls.s[i];
        x.val = sidx / x.vbl->stepsz;
        sidx = sidx % x.vbl->stepsz;
        if (i > 0)  oput_cstr_OFileB (of, " && ");
        oput_XnEVbl (of, &x, "==");
    }
}

    void
oput_promela_XnRule (OFileB* of, const XnRule* g, const XnSys* sys)
{
    bool had;
    XnPc* pc = &sys->pcs.s[g->pc];
    TableT(XnSz) t;
    oput_cstr_OFileB (of, "/*P");
    oput_uint_OFileB (of, g->pc);
    oput_cstr_OFileB (of, "*/ ");

    t = rvbls_XnPc (pc);
    had = false;
    {:for (i ; sys->vbls.sz)
        {:for (j ; t.sz)
            if (t.s[j] == i)
            {
                XnEVbl x;
                x.vbl = &sys->vbls.s[i];
                x.val = g->p.s[j];
                if (had)  oput_cstr_OFileB (of, " && ");
                had = true;
                oput_XnEVbl (of, &x, "==");
            }
        }
    }

    oput_cstr_OFileB (of, " ->");

    t = wvbls_XnPc (pc);
    {:for (i ; sys->vbls.sz)
        {:for (j ; t.sz)
            if (t.s[j] == i)
            {
                XnEVbl x;
                oput_char_OFileB (of, ' ');
                x.vbl = &sys->vbls.s[i];
                x.val = g->q.s[j];
                oput_XnEVbl (of, &x, "=");
                oput_char_OFileB (of, ';');
            }
        }
    }
}
    void
oput_promela_select (OFileB* of, const XnVbl* vbl)
{
    XnEVbl x;
    x.vbl = vbl;
    oput_cstr_OFileB (of, "if\n");
    {:for (i ; vbl->domsz)
        x.val = i;
        oput_cstr_OFileB (of, ":: true -> ");
        oput_XnEVbl (of, &x, "=");
        oput_cstr_OFileB (of, ";\n");
    }

    oput_cstr_OFileB (of, "fi;\n");
}

    void
oput_promela_pc (OFileB* of, const XnPc* pc, const XnSys* sys,
                 const TableT(XnRule) rules)
{
    const uint pcidx = IdxEltTable (sys->pcs, pc);
    oput_cstr_OFileB (of, "proctype P");
    oput_uint_OFileB (of, pcidx);
    oput_cstr_OFileB (of, " ()\n{\n");

    {
        bool found = false;
        for (XnSz i = 0; i < rules.sz; ++i)
            if (rules.s[i].pc == pcidx)
                found = true;
        if (!found)
        {
            oput_cstr_OFileB (of, "skip;\n}\n\n");
            return;
        }
    }

    oput_cstr_OFileB (of, "end_");
    oput_uint_OFileB (of, pcidx);
    oput_cstr_OFileB (of, ":\n");
    oput_cstr_OFileB (of, "do\n");
    {:for (i ; rules.sz)
        const XnRule* g = &rules.s[i];
        if (g->pc == pcidx)
        {
            oput_cstr_OFileB (of, ":: atomic {");
            oput_promela_XnRule (of, g, sys);
            oput_cstr_OFileB (of, "};\n");
        }
    }
    oput_cstr_OFileB (of, "od;\n");
    oput_cstr_OFileB (of, "}\n\n");
    
}

    void
oput_promela (OFileB* of, const XnSys* sys, const TableT(XnRule) rules)
{
#define oputl(s)  oput_cstr_OFileB(of, s); oput_char_OFileB(of, '\n')
    oputl( "/*** Use acceptance cycle check with the LTL claim for a full verification!" );
    oputl( " *** Assertions, end states, and progress conditions are present to help debugging." );
    oputl( " *** A safety check and liveness check (BOTH WITH LTL CLAIM DISABLED) should be" );
    oputl( " *** equivalent to verifying the LTL claim holds via the acceptance cycle check." );
    oputl( " ***/" );
    oputl( "bool Legit = false;" );
    {:for (i ; sys->vbls.sz)
        const XnVbl* x = &sys->vbls.s[i];
        if (x->domsz <= 2)
            oput_cstr_OFileB (of, "bit");
        else
            oput_cstr_OFileB (of, "byte");

        oput_char_OFileB (of, ' ');
        oput_AlphaTab (of, &x->name );
        oput_cstr_OFileB (of, ";\n");
    }

    for (uint i = 0; i < sys->pcs.sz; ++i)
        oput_promela_pc (of, &sys->pcs.s[i], sys, rules);

    oputl( "init {" );
    {:for (i ; sys->vbls.sz)
        const XnVbl* x = &sys->vbls.s[i];
        oput_promela_select (of, x);
    }

    {:for (i ; sys->pcs.sz)
        oput_cstr_OFileB (of, "run P");
        oput_uint_OFileB (of, i);
        oput_cstr_OFileB (of, " ();\n");
    }

    oputl( "if" );
    {:for (i ; sys->legit.sz)
        if (test_BitTable (sys->legit, i))
        {
            oput_cstr_OFileB (of, ":: ");
            oput_promela_state_XnSys (of, sys, i);
            oput_cstr_OFileB (of, " -> skip;\n");
        }
    }
    oputl( "fi;" );

    oputl( "Legit = true;" );
    oputl( "progress: skip;" );

    oputl( "end:" );
    oputl( "if" );
    for (ujint i = 0; i < sys->legit.sz; ++i)
    {
        if (!test_BitTable (sys->legit, i))
        {
            oput_cstr_OFileB (of, ":: ");
            oput_promela_state_XnSys (of, sys, i);
            oput_cstr_OFileB (of, " -> skip;\n");
        }
    }
    oputl( "fi;" );
    oputl( "Legit = false;" );
    oputl( "assert(0);" );
    oputl( "}" );

    oputl( "ltl {" );
    oputl( "<> Legit && [] (Legit -> [] Legit)" );
    oputl( "}" );
#undef oputl
}

