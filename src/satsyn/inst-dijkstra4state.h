/**
 * \file inst-dijkstra4state.h
 *
 * Dijkstra's token passing "spring" of 4 states per process.
 **/

static
    XnSys
inst_dijkstra4state_XnSys (uint npcs)
{
    DeclTable( uint, x_idcs );
    DeclTable( uint, up_idcs );
    DeclTable( XnDomSz, vs );
    XnSys sys[] = {DEFAULT_XnSys};
    OFile name[] = {DEFAULT_OFile};


    /* bottom:
     * x up=true
     *   reads x from right
     *   reads up from right
     * others:
     * x up
     *   reads x from both left and right
     *   reads up from right
     * top:
     * x up=false
     *   reads x from left
     */

    for (uint r = 0; r < npcs+2; ++r) {
        PushTable( sys->pcs, dflt_XnPc () );
    }

    /* Make processes and variables.*/
    for (uint r = 0; r < npcs; ++r) {
        XnVbl x_vbl = dflt_XnVbl ();
        XnVbl up_vbl = dflt_XnVbl ();

        x_vbl.domsz = 2;
        flush_OFile (name);
        printf_OFile (name, "x%u", r);
        copy_AlphaTab_OFile (&x_vbl.name, name);
        PushTable( x_idcs, sys->vbls.sz );
        PushTable( sys->vbls, x_vbl );

        up_vbl.domsz = 2;
        flush_OFile (name);
        printf_OFile (name, "up%u", r);
        copy_AlphaTab_OFile (&up_vbl.name, name);
        PushTable( up_idcs, sys->vbls.sz );
        PushTable( sys->vbls, up_vbl );
    }

    assoc_XnSys (sys, npcs, up_idcs.s[0], Yes);
    assoc_XnSys (sys, npcs+1, up_idcs.s[npcs-1], Yes);

    /* Make spring topology.*/
    for (uint r = 0; r < npcs; ++r) {
        assoc_XnSys (sys, r, x_idcs.s[r], Yes);
        if (0 < r && r < npcs-1) {
            assoc_XnSys (sys, r, up_idcs.s[r], Yes);
        }
        if (r > 0) {
            assoc_XnSys (sys, r, x_idcs.s[r-1], May);
        }
        if (r < npcs-1) {
            assoc_XnSys (sys, r, x_idcs.s[r+1], May);
            assoc_XnSys (sys, r, up_idcs.s[r+1], May);
        }
    }

    sys->syn_legit = true;
    accept_topology_XnSys (sys);

    for (uint sidx = 0; sidx < sys->nstates; ++sidx) {
        uint ntokens = 0;
        statevs_of_XnSys (&vs, sys, sidx);
        for (uint r = 0; r < npcs; ++r) {
            if (r == 0) {
                ntokens +=
                    ((vs.s[x_idcs.s[r]] == vs.s[x_idcs.s[r+1]] &&
                      vs.s[up_idcs.s[r+1]] == 0)
                     ? 1 : 0);
            }
            else if (r < npcs-1) {
                ntokens +=
                    (((vs.s[x_idcs.s[r]] != vs.s[x_idcs.s[r-1]])
                      ||
                      (vs.s[x_idcs.s[r]] == vs.s[x_idcs.s[r+1]] &&
                       vs.s[up_idcs.s[r]] == 1 &&
                       vs.s[up_idcs.s[r+1]] == 0))
                     ? 1 : 0);
            }
            else {
                ntokens +=
                    ((vs.s[x_idcs.s[r]] != vs.s[x_idcs.s[r-1]])
                     ? 1 : 0);
            }
        }
        setb_BitTable (sys->legit, sidx,
                       (ntokens == 1) &&
                       vs.s[up_idcs.s[0]] == 1 &&
                       vs.s[up_idcs.s[npcs-1]] == 0);
    }

    lose_OFile (name);
    LoseTable( vs );
    LoseTable( x_idcs );
    LoseTable( up_idcs );
    return *sys;
}

