/**
 * \file inst-dijkstra.c
 *
 * Dijkstra's token ring.
 **/

static
    XnSys
inst_dijkstra_XnSys (uint npcs)
{
    DeclTable( uint, x_idcs );
    DeclTable( XnDomSz, vs );
    DecloStack1( XnSys, sys, dflt_XnSys () );
    OFile name[1];
    init_OFile( name );

    /* Make processes and variables.*/
    {:for (r ; npcs)
        XnVbl x_vbl = dflt_XnVbl ();
        PushTable( sys->pcs, dflt_XnPc () );

        x_vbl.domsz = npcs + 1;
        flush_OFile (name);
        printf_OFile (name, "x%u", r);
        copy_AlphaTab_OFile (&x_vbl.name, name);
        PushTable( x_idcs, sys->vbls.sz );
        PushTable( sys->vbls, x_vbl );
    }

    /* Make unidirectional ring topology.*/
    {:for (r ; npcs)
        assoc_XnSys (sys, r, x_idcs.s[r], Yes);
        assoc_XnSys (sys, r, x_idcs.s[dec1mod (r, npcs)], May);
    }

    sys->syn_legit = true;
    accept_topology_XnSys (sys);

    {:for (sidx ; sys->nstates)
        uint ntokens = 0;
        statevs_of_XnSys (&vs, sys, sidx);
        {:for (r ; npcs)
            ntokens +=
                (vs.s[x_idcs.s[r]] == vs.s[x_idcs.s[dec1mod (r, npcs)]]
                 ? (r == 0 ? 1 : 0)
                 : (r == 0 ? 0 : 1));
        }
        setb_BitTable (sys->legit, sidx, (ntokens == 1));
    }

    lose_OFile (name);
    LoseTable( vs );
    LoseTable( x_idcs );
    return *sys;
}

