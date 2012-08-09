/**
 * \file inst-coloring.c
 * Ring coloring instance!
 **/

static
    XnSys
inst_coloring_XnSys (uint npcs, uint dom_max)
{
    DeclTable( DomSz, vs );
    DecloStack1( XnSys, sys, dflt_XnSys () );
    OFileB name = dflt_OFileB ();

    /* Make processes and variables.*/
    { BLoop( r, npcs )
        XnVbl vbl = dflt_XnVbl ();

        vbl.max = dom_max;

        flush_OFileB (&name);
        printf_OFileB (&name, "c%u", r);
        copy_AlphaTab_OFileB (&vbl.name, &name);

        PushTable( sys->pcs, dflt_XnPc () );
        PushTable( sys->vbls, vbl );
    } BLose()

    /* Make bidirectional ring topology.*/
    { BLoop( r, npcs )
        assoc_XnSys (sys, r, r, Yes);
        assoc_XnSys (sys, r, dec1mod (r, npcs), May);
        assoc_XnSys (sys, r, inc1mod (r, npcs), May);
    } BLose()

    accept_topology_XnSys (sys);

    { BUjFor( sidx, sys->nstates )
        bool good = true;
        statevs_of_XnSys (&vs, sys, sidx);
        { BLoop( r, npcs )
            good =
                (vs.s[r] != vs.s[dec1mod (r, npcs)]) &&
                (vs.s[r] != vs.s[inc1mod (r, npcs)]);
            if (!good)  break;
        } BLose()
        setb_BitTable (sys->legit, sidx, good);
    } BLose()

    lose_OFileB (&name);
    LoseTable( vs );
    return *sys;
}

