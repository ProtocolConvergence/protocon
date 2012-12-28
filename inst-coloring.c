/**
 * \file inst-coloring.c
 * Ring coloring instance!
 **/

static
    XnSys
inst_coloring_XnSys (uint npcs, uint domsz)
{
    DeclTable( XnDomSz, vs );
    DecloStack1( XnSys, sys, dflt_XnSys () );
    OFileB name = dflt_OFileB ();

#if 0
    const bool symmetric = true;
    if (symmetric)
    {
        XnPcSymm pc = cons1_XnPcSymm ("P");
        add_vbl_XnPcSymm (&pc, "c-", 3, Nil);
        add_vbl_XnPcSymm (&pc, "c+", 3, Nil);
        add_vbl_XnPcSymm (&pc, "c" , 3, Yes);
        PushTable( sys->pcsymms, pc );
    }
#endif

    /* Make processes and variables.*/
    {:for (r ; npcs)
        XnVbl vbl = dflt_XnVbl ();

        vbl.domsz = domsz;

        flush_OFileB (&name);
        printf_OFileB (&name, "c%u", r);
        copy_AlphaTab_OFileB (&vbl.name, &name);

        PushTable( sys->pcs, dflt_XnPc () );
        PushTable( sys->vbls, vbl );
    }

    /* Make bidirectional ring topology.*/
    {:for (r ; npcs)
        assoc_XnSys (sys, r, r, Yes);
        assoc_XnSys (sys, r, dec1mod (r, npcs), May);
        assoc_XnSys (sys, r, inc1mod (r, npcs), May);
    }

    accept_topology_XnSys (sys);

    {:for (sidx ; sys->nstates)
        bool good = true;
        statevs_of_XnSys (&vs, sys, sidx);
        {:for (r ; npcs)
            good =
                (vs.s[r] != vs.s[dec1mod (r, npcs)]) &&
                (vs.s[r] != vs.s[inc1mod (r, npcs)]);
            if (!good)  break;
        }
        setb_BitTable (sys->legit, sidx, good);
    }

    lose_OFileB (&name);
    LoseTable( vs );
    return *sys;
}

