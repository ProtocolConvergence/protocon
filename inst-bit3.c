/**
 * \file inst-bit3.c
 *
 * 3-bit token ring... kind of.
 * There is no way to enforce that a token can be passed
 * without giving away the entire protocol!
 **/

static
    XnSys
inst_bit3_XnSys (uint npcs)
{
    DeclTable( uint, e_idcs );
    DeclTable( uint, t_idcs );
    DeclTable( uint, ready_idcs );
    DeclTable( DomSz, vs );
    DecloStack1( XnSys, sys, dflt_XnSys () );
    OFileB name = dflt_OFileB ();

    /* Make processes and variables.*/
    { BLoop( r, npcs )
        XnVbl e_vbl = dflt_XnVbl ();
        XnVbl t_vbl = dflt_XnVbl ();
        XnVbl ready_vbl = dflt_XnVbl ();

        PushTable( sys->pcs, dflt_XnPc () );

        e_vbl.domsz = 2;
        flush_OFileB (&name);
        printf_OFileB (&name, "e%u", r);
        copy_AlphaTab_OFileB (&e_vbl.name, &name);
        PushTable( e_idcs, sys->vbls.sz );
        PushTable( sys->vbls, e_vbl );

        t_vbl.domsz = 2;
        flush_OFileB (&name);
        printf_OFileB (&name, "t%u", r);
        copy_AlphaTab_OFileB (&t_vbl.name, &name);
        PushTable( t_idcs, sys->vbls.sz );
        PushTable( sys->vbls, t_vbl );

        ready_vbl.domsz = 2;
        flush_OFileB (&name);
        printf_OFileB (&name, "ready%u", r);
        copy_AlphaTab_OFileB (&ready_vbl.name, &name);
        PushTable( ready_idcs, sys->vbls.sz );
        PushTable( sys->vbls, ready_vbl );
    } BLose()

    /* Make bidirectional ring topology.*/
    { BLoop( r, npcs )
        assoc_XnSys (sys, r, e_idcs.s[r], Yes);
        assoc_XnSys (sys, r, t_idcs.s[r], Yes);
        assoc_XnSys (sys, r, ready_idcs.s[r], Yes);
        assoc_XnSys (sys, r, e_idcs.s[dec1mod (r, npcs)], May);
        assoc_XnSys (sys, r, t_idcs.s[dec1mod (r, npcs)], May);
    } BLose()

    sys->syn_legit = true;
    accept_topology_XnSys (sys);

    { BUjFor( sidx, sys->nstates )
        uint ntokens = 0;
        uint nenabled = 0;
        statevs_of_XnSys (&vs, sys, sidx);
        { BLoop( r, npcs )
            ntokens +=
                (vs.s[t_idcs.s[r]] == vs.s[t_idcs.s[dec1mod (r, npcs)]]
                 ? (r == 0 ? 1 : 0)
                 : (r == 0 ? 0 : 1));
            nenabled +=
                (vs.s[e_idcs.s[r]] == vs.s[e_idcs.s[dec1mod (r, npcs)]]
                 ? (r == 0 ? 1 : 0)
                 : (r == 0 ? 0 : 1));
        } BLose()
        setb_BitTable (sys->legit, sidx, (ntokens == 1 && nenabled >= 1));
    } BLose()

    lose_OFileB (&name);
    LoseTable( vs );
    LoseTable( e_idcs );
    LoseTable( t_idcs );
    LoseTable( ready_idcs );
    return *sys;
}

