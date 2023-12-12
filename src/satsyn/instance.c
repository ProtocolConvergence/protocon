
#include "instance.h"

/**
 * Ring coloring instance!
 **/
  XnSys
inst_coloring_XnSys(unsigned npcs, unsigned domsz)
{
  DeclTable( XnDomSz, vs );
  XnSys sys[] = {DEFAULT_XnSys};
  FildeshO name[] = {DEFAULT_FildeshO};

#if 0
  const bool symmetric = true;
  if (symmetric)
  {
    XnPcSymm pc = cons1_XnPcSymm("P");
    add_vbl_XnPcSymm(&pc, "c-", 3, Nil);
    add_vbl_XnPcSymm(&pc, "c+", 3, Nil);
    add_vbl_XnPcSymm(&pc, "c" , 3, Yes);
    PushTable( sys->pcsymms, pc );
  }
#endif

  /* Make processes and variables.*/
  for (unsigned r = 0; r < npcs; ++r) {
    XnVbl vbl = dflt_XnVbl();

    vbl.domsz = domsz;

    truncate_FildeshO(name);
    putc_FildeshO(name, 'c');
    print_int_FildeshO(name, (int)r);
    putc_FildeshO(name, '\0');
    assign_name_of_XnVbl(&vbl, name->at);

    PushTable( sys->pcs, dflt_XnPc() );
    PushTable( sys->vbls, vbl );
  }

  /* Make bidirectional ring topology.*/
  for (unsigned r = 0; r < npcs; ++r) {
    assoc_XnSys(sys, r, r, Yes);
    assoc_XnSys(sys, r, dec1mod(r, npcs), May);
    assoc_XnSys(sys, r, inc1mod(r, npcs), May);
  }

  accept_topology_XnSys(sys);

  for (unsigned sidx = 0; sidx < sys->nstates; ++sidx) {
    bool good = true;
    statevs_of_XnSys(&vs, sys, sidx);
    for (unsigned r = 0; r < npcs; ++r) {
      good =
        (vs.s[r] != vs.s[dec1mod(r, npcs)]) &&
        (vs.s[r] != vs.s[inc1mod(r, npcs)]);
      if (!good)  break;
    }
    setb_BitTable(sys->legit, sidx, good);
  }

  close_FildeshO(name);
  LoseTable( vs );
  return *sys;
}

/**
 * Maximal matching instance!
 **/
  XnSys
inst_matching_XnSys(unsigned npcs)
{
  DeclTable( XnDomSz, vs );
  XnSys sys[] = {DEFAULT_XnSys};
  FildeshO name[] = {DEFAULT_FildeshO};

  /* Make processes and variables.*/
  for (unsigned r = 0; r < npcs; ++r) {
    XnVbl vbl = dflt_XnVbl();

    vbl.domsz = 3;

    truncate_FildeshO(name);
    putc_FildeshO(name, 'm');
    print_int_FildeshO(name, (int)r);
    putc_FildeshO(name, '\0');
    assign_name_of_XnVbl(&vbl, name->at);

    PushTable( sys->pcs, dflt_XnPc() );
    PushTable( sys->vbls, vbl );
  }

  /* Make bidirectional ring topology.*/
  for (unsigned r = 0; r < npcs; ++r) {
    assoc_XnSys(sys, r, r, Yes);
    assoc_XnSys(sys, r, dec1mod(r, npcs), May);
    assoc_XnSys(sys, r, inc1mod(r, npcs), May);
  }

  accept_topology_XnSys(sys);

  for (unsigned sidx = 0; sidx < sys->nstates; ++sidx) {
    bool good = true;
    statevs_of_XnSys(&vs, sys, sidx);
    for (unsigned r = 0; r < npcs; ++r) {
      bool self =
        (vs.s[r] == 0) &&
        (vs.s[dec1mod(r, npcs)] == 1) &&
        (vs.s[inc1mod(r, npcs)] == 2);
      bool left =
        (vs.s[r] == 1) &&
        (vs.s[dec1mod(r, npcs)] == 2);
      bool right =
        (vs.s[r] == 2) &&
        (vs.s[inc1mod(r, npcs)] == 1);
      good = (self || left || right);
      if (!good)  break;
    }
    setb_BitTable(sys->legit, sidx, good);
  }

  close_FildeshO(name);
  LoseTable( vs );
  return *sys;
}

/**
 * 3-bit token ring... kind of.
 * There is no way to enforce that a token can be passed
 * without giving away the entire protocol!
 **/
  XnSys
inst_bit3_XnSys(unsigned npcs)
{
  DeclTable( uint, e_idcs );
  DeclTable( uint, t_idcs );
  DeclTable( uint, ready_idcs );
  DeclTable( XnDomSz, vs );
  XnSys sys[] = {DEFAULT_XnSys};
  FildeshO name[] = {DEFAULT_FildeshO};

  /* Make processes and variables.*/
  for (unsigned r = 0; r < npcs; ++r) {
    XnVbl e_vbl = dflt_XnVbl();
    XnVbl t_vbl = dflt_XnVbl();
    XnVbl ready_vbl = dflt_XnVbl();

    PushTable( sys->pcs, dflt_XnPc() );

    e_vbl.domsz = 2;
    truncate_FildeshO(name);
    putc_FildeshO(name, 'e');
    print_int_FildeshO(name, (int)r);
    putc_FildeshO(name, '\0');
    assign_name_of_XnVbl(&e_vbl, name->at);
    PushTable( e_idcs, sys->vbls.sz );
    PushTable( sys->vbls, e_vbl );

    t_vbl.domsz = 2;
    truncate_FildeshO(name);
    putc_FildeshO(name, 't');
    print_int_FildeshO(name, (int)r);
    putc_FildeshO(name, '\0');
    assign_name_of_XnVbl(&t_vbl, name->at);
    PushTable( t_idcs, sys->vbls.sz );
    PushTable( sys->vbls, t_vbl );

    ready_vbl.domsz = 2;
    truncate_FildeshO(name);
    putstrlit_FildeshO(name, "ready");
    print_int_FildeshO(name, (int)r);
    putc_FildeshO(name, '\0');
    assign_name_of_XnVbl(&ready_vbl, name->at);
    PushTable( ready_idcs, sys->vbls.sz );
    PushTable( sys->vbls, ready_vbl );
  }

  /* Make bidirectional ring topology.*/
  for (unsigned r = 0; r < npcs; ++r) {
    assoc_XnSys(sys, r, e_idcs.s[r], Yes);
    assoc_XnSys(sys, r, t_idcs.s[r], Yes);
    assoc_XnSys(sys, r, ready_idcs.s[r], Yes);
    assoc_XnSys(sys, r, e_idcs.s[dec1mod(r, npcs)], May);
    assoc_XnSys(sys, r, t_idcs.s[dec1mod(r, npcs)], May);
  }

  sys->syn_legit = true;
  accept_topology_XnSys(sys);

  for (unsigned sidx = 0; sidx < sys->nstates; ++sidx) {
    unsigned ntokens = 0;
    unsigned nenabled = 0;
    statevs_of_XnSys(&vs, sys, sidx);
    for (unsigned r = 0; r < npcs; ++r) {
      ntokens +=
        (vs.s[t_idcs.s[r]] == vs.s[t_idcs.s[dec1mod(r, npcs)]]
         ? (r == 0 ? 1 : 0)
         : (r == 0 ? 0 : 1));
      nenabled +=
        (vs.s[e_idcs.s[r]] == vs.s[e_idcs.s[dec1mod(r, npcs)]]
         ? (r == 0 ? 1 : 0)
         : (r == 0 ? 0 : 1));
    }
    setb_BitTable(sys->legit, sidx,(ntokens == 1 && nenabled >= 1));
  }

  close_FildeshO(name);
  LoseTable( vs );
  LoseTable( e_idcs );
  LoseTable( t_idcs );
  LoseTable( ready_idcs );
  return *sys;
}

/**
 * Dijkstra's token ring.
 **/
  XnSys
inst_dijkstra_XnSys(unsigned npcs)
{
  DeclTable( uint, x_idcs );
  DeclTable( XnDomSz, vs );
  XnSys sys[] = {DEFAULT_XnSys};
  FildeshO name[] = {DEFAULT_FildeshO};

  /* Make processes and variables.*/
  for (unsigned r = 0; r < npcs; ++r) {
    XnVbl x_vbl = dflt_XnVbl();
    PushTable( sys->pcs, dflt_XnPc() );

    x_vbl.domsz = npcs + 1;
    truncate_FildeshO(name);
    putc_FildeshO(name, 'x');
    print_int_FildeshO(name, (int)r);
    putc_FildeshO(name, '\0');
    assign_name_of_XnVbl(&x_vbl, name->at);
    PushTable( x_idcs, sys->vbls.sz );
    PushTable( sys->vbls, x_vbl );
  }

  /* Make unidirectional ring topology.*/
  for (unsigned r = 0; r < npcs; ++r) {
    assoc_XnSys(sys, r, x_idcs.s[r], Yes);
    assoc_XnSys(sys, r, x_idcs.s[dec1mod(r, npcs)], May);
  }

  sys->syn_legit = true;
  accept_topology_XnSys(sys);

  for (unsigned sidx = 0; sidx < sys->nstates; ++sidx) {
    unsigned ntokens = 0;
    statevs_of_XnSys(&vs, sys, sidx);
    for (unsigned r = 0; r < npcs; ++r) {
      ntokens +=
        (vs.s[x_idcs.s[r]] == vs.s[x_idcs.s[dec1mod(r, npcs)]]
         ? (r == 0 ? 1 : 0)
         : (r == 0 ? 0 : 1));
    }
    setb_BitTable(sys->legit, sidx,(ntokens == 1));
  }

  close_FildeshO(name);
  LoseTable( vs );
  LoseTable( x_idcs );
  return *sys;
}

/**
 * Dijkstra's token passing "spring" of 4 states per process.
 **/
  XnSys
inst_dijkstra4state_XnSys(unsigned npcs)
{
  DeclTable( uint, x_idcs );
  DeclTable( uint, up_idcs );
  DeclTable( XnDomSz, vs );
  XnSys sys[] = {DEFAULT_XnSys};
  FildeshO name[] = {DEFAULT_FildeshO};


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

  for (unsigned r = 0; r < npcs+2; ++r) {
    PushTable( sys->pcs, dflt_XnPc() );
  }

  /* Make processes and variables.*/
  for (unsigned r = 0; r < npcs; ++r) {
    XnVbl x_vbl = dflt_XnVbl();
    XnVbl up_vbl = dflt_XnVbl();

    x_vbl.domsz = 2;
    truncate_FildeshO(name);
    putc_FildeshO(name, 'x');
    print_int_FildeshO(name, (int)r);
    putc_FildeshO(name, '\0');
    assign_name_of_XnVbl(&x_vbl, name->at);
    PushTable( x_idcs, sys->vbls.sz );
    PushTable( sys->vbls, x_vbl );

    up_vbl.domsz = 2;
    truncate_FildeshO(name);
    putstrlit_FildeshO(name, "up");
    print_int_FildeshO(name, (int)r);
    putc_FildeshO(name, '\0');
    assign_name_of_XnVbl(&up_vbl, name->at);
    PushTable( up_idcs, sys->vbls.sz );
    PushTable( sys->vbls, up_vbl );
  }

  assoc_XnSys(sys, npcs, up_idcs.s[0], Yes);
  assoc_XnSys(sys, npcs+1, up_idcs.s[npcs-1], Yes);

  /* Make spring topology.*/
  for (unsigned r = 0; r < npcs; ++r) {
    assoc_XnSys(sys, r, x_idcs.s[r], Yes);
    if (0 < r && r < npcs-1) {
      assoc_XnSys(sys, r, up_idcs.s[r], Yes);
    }
    if (r > 0) {
      assoc_XnSys(sys, r, x_idcs.s[r-1], May);
    }
    if (r < npcs-1) {
      assoc_XnSys(sys, r, x_idcs.s[r+1], May);
      assoc_XnSys(sys, r, up_idcs.s[r+1], May);
    }
  }

  sys->syn_legit = true;
  accept_topology_XnSys(sys);

  for (unsigned sidx = 0; sidx < sys->nstates; ++sidx) {
    unsigned ntokens = 0;
    statevs_of_XnSys(&vs, sys, sidx);
    for (unsigned r = 0; r < npcs; ++r) {
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
    setb_BitTable(sys->legit, sidx,
                  (ntokens == 1) &&
                  vs.s[up_idcs.s[0]] == 1 &&
                  vs.s[up_idcs.s[npcs-1]] == 0);
  }

  close_FildeshO(name);
  LoseTable( vs );
  LoseTable( x_idcs );
  LoseTable( up_idcs );
  return *sys;
}

