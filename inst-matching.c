/**
 * \file inst-matching.c
 * Maximal matching instance!
 **/

static
    XnSys
inst_matching_XnSys (uint npcs)
{
    DeclTable( DomSz, vs );
    DecloStack1( XnSys, sys, dflt_XnSys () );
    OFileB name = dflt_OFileB ();

    /* Make processes and variables.*/
    { BLoop( r, npcs )
        XnVbl vbl = dflt_XnVbl ();

        vbl.domsz = 3;

        flush_OFileB (&name);
        printf_OFileB (&name, "m%u", r);
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
            bool self =
                (vs.s[r] == 0) &&
                (vs.s[dec1mod (r, npcs)] == 1) &&
                (vs.s[inc1mod (r, npcs)] == 2);
            bool left =
                (vs.s[r] == 1) &&
                (vs.s[dec1mod (r, npcs)] == 2);
            bool right =
                (vs.s[r] == 2) &&
                (vs.s[inc1mod (r, npcs)] == 1);
            good = (self || left || right);
            if (!good)  break;
        } BLose()
        setb_BitTable (sys->legit, sidx, good);
    } BLose()

    lose_OFileB (&name);
    LoseTable( vs );
    return *sys;
}

