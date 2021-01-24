/**
 * \file inst-coloring.h
 * Ring coloring instance!
 **/

static
    XnSys
inst_coloring_XnSys (uint npcs, uint domsz)
{
    DeclTable( XnDomSz, vs );
    XnSys sys[] = {DEFAULT_XnSys};
    OFile name[] = {DEFAULT_OFile};

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
    for (uint r = 0; r < npcs; ++r) {
        XnVbl vbl = dflt_XnVbl ();

        vbl.domsz = domsz;

        flush_OFile (name);
        printf_OFile (name, "c%u", r);
        copy_AlphaTab_OFile (&vbl.name, name);

        PushTable( sys->pcs, dflt_XnPc () );
        PushTable( sys->vbls, vbl );
    }

    /* Make bidirectional ring topology.*/
    for (uint r = 0; r < npcs; ++r) {
        assoc_XnSys (sys, r, r, Yes);
        assoc_XnSys (sys, r, dec1mod (r, npcs), May);
        assoc_XnSys (sys, r, inc1mod (r, npcs), May);
    }

    accept_topology_XnSys (sys);

    for (uint sidx = 0; sidx < sys->nstates; ++sidx) {
        bool good = true;
        statevs_of_XnSys (&vs, sys, sidx);
        for (uint r = 0; r < npcs; ++r) {
            good =
                (vs.s[r] != vs.s[dec1mod (r, npcs)]) &&
                (vs.s[r] != vs.s[inc1mod (r, npcs)]);
            if (!good)  break;
        }
        setb_BitTable (sys->legit, sidx, good);
    }

    lose_OFile (name);
    LoseTable( vs );
    return *sys;
}

