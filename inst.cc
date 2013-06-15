/**
 * \file inst.cc
 *
 * Functions to set up problem instances.
 */

#include "inst.hh"
#include "xnsys.hh"
#include <stdio.h>

/** Increment followed by modulo.**/
static
  uint
incmod(uint i, uint by, uint n)
{
  return (i + by) % n;
}

/** Decrement followed by modulo.**/
static
  uint
decmod(uint i, uint by, uint n)
{
  return (i + n - (by % n)) % n;
}

/** Create a unidirectional ring topology.**/
static
  void
UnidirectionalRing(Xn::Net& topo, uint npcs, uint domsz,
                   const char* basename, bool symmetric, bool distinguished)
{
  // Build a unidirectional ring where each process P_i
  Xn::VblSymm* vbl_symm = topo.add_variables(basename, npcs, domsz);

  Claim( symmetric || !distinguished );

  if (distinguished) {
    -- npcs;
  }

  if (symmetric) {
    Xn::PcSymm* pc_symm = topo.add_processes("P", npcs);

    // Make this f(i) = i-1
    Xn::NatMap indices(npcs);
    for (uint i = 0; i < npcs; ++i) {
      indices.membs[i] = (int)i - 1;
    }
    indices.expression_chunks.push("-1");
    topo.add_read_access(pc_symm, vbl_symm, indices);

    // Now make this f(i) = i
    indices = Xn::NatMap(npcs);
    for (uint i = 0; i < npcs; ++i) {
      indices.membs[i] = (int)i;
    }
    indices.expression_chunks.push("");
    topo.add_write_access(pc_symm, vbl_symm, indices);
  }
  else {
    // Create a new symmetry for each process.
    for (uint i = 0; i < npcs; ++i) {
      Xn::PcSymm* pc_symm = topo.add_processes(Xn::String("P") + i, 1);

      // Make this f(j) = i-1
      Xn::NatMap indices(1);
      indices.membs[0] = (int)i - 1;
      indices.expression_chunks[0] = indices.membs[0];
      topo.add_read_access(pc_symm, vbl_symm, indices);

      // Now make this f(j) = i
      indices.membs[0] = (int)i;
      indices.expression_chunks[0] = indices.membs[0];
      topo.add_write_access(pc_symm, vbl_symm, indices);
    }
  }

  if (distinguished) {
    ++ npcs;

    Xn::PcSymm* pc_symm = topo.add_processes("Bot", 1);

    Xn::NatMap indices(1);
    indices.membs[0] = (int)npcs - 2;
    indices.expression_chunks[0] = indices.membs[0];
    topo.add_read_access(pc_symm, vbl_symm, indices);

    indices.membs[0] = (int)npcs - 1;
    indices.expression_chunks[0] = indices.membs[0];
    topo.add_write_access(pc_symm, vbl_symm, indices);
  }
}

/** Create a bidirectional ring topology.
 **/
static
  void
BidirectionalRing(Xn::Net& topo, uint npcs, uint domsz,
                  const char* basename, bool symmetric)
{
  // Build a bidirectional ring where each process P_i
  // has variable m_i of domain size 3.
  UnidirectionalRing(topo, npcs, domsz, basename, symmetric, false);

  if (symmetric) {
    Xn::PcSymm* pc_symm = &topo.pc_symms[0];

    // Make this f(i) = i+1
    Xn::NatMap indices(npcs);
    for (uint i = 0; i < npcs; ++i) {
      indices.membs[i] = (int)i + 1;
    }
    indices.expression_chunks.push("+1");
    topo.add_read_access(pc_symm, &topo.vbl_symms[0], indices);
  }
  else {
    for (uint i = 0; i < npcs; ++i) {
      Xn::PcSymm* pc_symm = &topo.pc_symms[i];
      // Make this f(j) = i+1
      Xn::NatMap indices(1);
      indices.membs[0] = (int)i + 1;
      indices.expression_chunks[0] = indices.membs[0];
      topo.add_read_access(pc_symm, &topo.vbl_symms[0], indices);
    }
  }
}


/**
 * Performs the 3 color on a ring problem.  Each process must be assigned
 * a color such that it'd color is not the same as either of its
 * neighbors.  The domain is [0,2], corresponding to each of 3 arbitrary
 * colors.
 *
 * \param sys  The system context
 * \param npcs The number of processes
 */
  void
InstThreeColoringRing(Xn::Sys& sys, uint npcs)
{
  Xn::Net& topo = sys.topology;
  BidirectionalRing(topo, npcs, 3, "c", true);

  sys.commit_initialization();
  sys.invariant = true;

  for (uint pcidx = 0; pcidx < npcs; ++pcidx) {
    const Xn::Pc& pc = topo.pcs[pcidx];
    const Cx::PFmlaVbl m_p = topo.pfmla_vbl (*pc.rvbls[0]);
    const Cx::PFmlaVbl m_r = topo.pfmla_vbl (*pc.rvbls[1]);
    const Cx::PFmlaVbl m_s = topo.pfmla_vbl (*pc.rvbls[2]);

    sys.invariant &= (m_p != m_r) && (m_r != m_s);
  }
}


/**
 * Return the states for which only one process has a token.
 * \param tokenPFs  Formulas for each process having a token.
 */
static
  PF
SingleTokenPF(const vector<PF>& tokenPFs)
{
  const uint n = tokenPFs.size();
  vector<PF> singleToken(n, PF(true));
  for (uint i = 0; i < n; ++i) {
    for (uint j = 0; j < n; ++j) {
      if (j == i) {
        // Process pcIdx has the only token
        // in the /singleToken[j]/ formula.
        singleToken[j] &= tokenPFs[i]; 
      }
      else {
        // Process pcIdx does not have a token
        // in the /singleToken[j]/ formula.
        singleToken[j] -= tokenPFs[i]; 
      }
    }
  }

  PF pf( false );
  for (uint i = 0; i < n; ++i) {
    pf |= singleToken[i];
  }
  return pf;
}

/**
 * Performs the 2 coloring on a ring problem.
 *
 * \param sys  Return value. The system context.
 * \param npcs The number of processes.
 */
  void
InstTwoColoringRing(Xn::Sys& sys, uint npcs)
{
  if (npcs % 2 == 1) {
    DBog1( "Number of processes is even (%u), this should fail!", npcs );
  }
  Xn::Net& topo = sys.topology;
  UnidirectionalRing(topo, npcs, 2, "c", false, false);

  sys.commit_initialization();
  sys.invariant = true;

  // For each process P[i],
  for (uint i = 0; i < npcs; ++i) {
    const Cx::PFmlaVbl c_p = topo.pfmla_vbl(decmod(i, 1, npcs));
    const Cx::PFmlaVbl c_r = topo.pfmla_vbl(i);
    sys.invariant &= (c_p != c_r);
  }
}

  void
InstMatching(Xn::Sys& sys, uint npcs, bool symmetric)
{
  Xn::Net& topo = sys.topology;
  BidirectionalRing(topo, npcs, 3, "x", symmetric);

  // Commit to using this topology.
  // MDD stuff is initialized.
  sys.commit_initialization();
  sys.invariant = true;

#if 0
  // Set priorities.
  for (uint pcidx = 0; pcidx < npcs; ++pcidx) {
    uint niceIdx0 = 2 * pcidx;
    uint niceIdx1 = 2 * (npcs - pcidx - 1) + 1;
    uint niceIdx = (niceIdx0 < niceIdx1) ? niceIdx0 : niceIdx1;
    sys.niceIdxFo(pcidx, niceIdx);
  }
#endif

  for (uint pcidx = 0; pcidx < npcs; ++pcidx) {
    const Xn::Pc& pc = topo.pcs[pcidx];
    const Cx::PFmlaVbl x_p = topo.pfmla_vbl (*pc.rvbls[0]);
    const Cx::PFmlaVbl x_r = topo.pfmla_vbl (*pc.rvbls[1]);
    const Cx::PFmlaVbl x_s = topo.pfmla_vbl (*pc.rvbls[2]);

    // 0 = Self, 1 = Left, 2 = Right
    sys.invariant &=
      (x_p == 1 && x_r == 0 && x_s == 2) || // ( left,  self, right)
      (x_p == 2 && x_r == 1            ) || // (right,  left,     X)
      (            x_r == 2 && x_s == 1);   // (    X, right,  left)
  }
}

/**
 * Set up a sum-not-(l-1) instance.
 * You are free to choose the domain size and the target (to miss).
 **/
  void
InstSumNot(Xn::Sys& sys, uint npcs, uint domsz, uint target, const char* vbl_name)
{
  Xn::Net& topo = sys.topology;
  UnidirectionalRing(topo, npcs, domsz, vbl_name, true, false);

  // Commit to using this topology.
  // MDD stuff is initialized.
  sys.commit_initialization();
  sys.invariant = true;

  for (uint pcidx = 0; pcidx < npcs; ++pcidx) {
    const Xn::Pc& pc = topo.pcs[pcidx];
    const Cx::PFmlaVbl x_p = topo.pfmla_vbl (*pc.rvbls[0]);
    const Cx::PFmlaVbl x_r = topo.pfmla_vbl (*pc.rvbls[1]);

    sys.invariant &= (x_p + x_r != (int) target);
  }
}

/** Agreement.
 * Only enforce that a subset of the invariant be closed.
 **/
  void
InstAgreementRing(Xn::Sys& sys, uint npcs, const char* vbl_name)
{
  Xn::Net& topo = sys.topology;
  BidirectionalRing(topo, npcs, npcs, vbl_name, true);

  // Commit to using this topology, and initilize MDD stuff
  sys.commit_initialization();
  sys.invariant = true;

#if 0
  // Set priorities.
  for (uint pcIdx = 0; pcIdx < npcs; ++pcIdx) {
    sys.niceIdxFo(pcIdx, npcs-pcIdx-1);
  }
#endif

  for (uint pcidx = 0; pcidx < npcs; ++pcidx) {
    const Xn::Pc& pc = topo.pcs[pcidx];
    const Cx::PFmlaVbl x_p = topo.pfmla_vbl (*pc.rvbls[0]);
    const Cx::PFmlaVbl x_r = topo.pfmla_vbl (*pc.rvbls[1]);
    const Cx::PFmlaVbl x_s = topo.pfmla_vbl (*pc.rvbls[2]);

    sys.invariant &= (((x_r - x_p) % npcs) == ((x_s - x_r) % npcs));
  }
}


/** Dijkstra's original token ring
 * with each process's variable with a domain of size N.
 **/
  void
InstDijkstraTokenRing(Xn::Sys& sys, uint npcs)
{
  Xn::Net& topo = sys.topology;
  UnidirectionalRing(topo, npcs, npcs, "x", true, true);

  // Commit to using this topology, and initilize MDD stuff
  sys.commit_initialization();
  sys.synLegit = true;
  sys.liveLegit = true;

#if 0
  // Set priorities.
  for (uint pcIdx = 0; pcIdx < npcs; ++pcIdx) {
    sys.niceIdxFo(pcIdx, npcs-pcIdx-1);
  }
#endif

  // Formulas for each process having a token.
  vector<PF> tokenPFs(npcs);
  for (uint i = 0; i < npcs-1; ++i) {
    // (x[i] != x[i-1])
    tokenPFs[i] = (topo.pfmla_vbl(decmod(i, 1, npcs)) != topo.pfmla_vbl(i));
  }
  // (x[N-2] == x[N-1])
  tokenPFs[npcs-1] = (topo.pfmla_vbl(npcs-2) == topo.pfmla_vbl(npcs-1));
  sys.invariant = SingleTokenPF(tokenPFs);
}

/** Gouda's three bit token ring.**/
  void
InstThreeBitTokenRing(Xn::Sys& sys, uint npcs)
{
  Xn::Net& topo = sys.topology;
  UnidirectionalRing(topo, npcs, 2, "e", true, true);

  topo.add_variables("t", npcs, 2);
  topo.add_variables("ready", npcs, 2);

  // Make this f(i) = i-1
  Xn::NatMap indices(npcs-1);
  for (uint i = 0; i < npcs-1; ++i) {
    indices.membs[i] = (int)i - 1;
  }
  indices.expression_chunks.push("-1");
  // P process reads t[i-1]
  topo.add_read_access(&topo.pc_symms[0], &topo.vbl_symms[1], indices);

  // Now make this f(i) = i
  indices = Xn::NatMap(npcs-1);
  for (uint i = 0; i < npcs-1; ++i) {
    indices.membs[i] = (int)i;
  }
  indices.expression_chunks.push("");
  // P process writes t[i] and ready[i]
  topo.add_write_access(&topo.pc_symms[0], &topo.vbl_symms[1], indices);
  topo.add_write_access(&topo.pc_symms[0], &topo.vbl_symms[2], indices);

  // Bot process reads t[n-2]
  indices = Xn::NatMap(1);
  indices.membs[0] = (int)npcs-2;
  indices.expression_chunks[0] = indices.membs[0];
  topo.add_read_access(&topo.pc_symms[1], &topo.vbl_symms[1], indices);

  // Bot process writes t[n-1]
  indices.membs[0] = (int)npcs-1;
  indices.expression_chunks[0] = indices.membs[0];
  topo.add_write_access(&topo.pc_symms[1], &topo.vbl_symms[1], indices);
  // Bot process writes ready[n-1]
  topo.add_write_access(&topo.pc_symms[1], &topo.vbl_symms[2], indices);

  // Commit to using this topology, and initilize MDD stuff
  sys.commit_initialization();
  sys.synLegit = true;
  sys.liveLegit = true;

#if 0
  sys.niceIdxFo(0, 1);
  sys.niceIdxFo(1, 0);
#endif

  // Formulas for each process having a token.
  vector<PF> tokenPFs(npcs);
  // Formula for existence of an enabled process.
  PF existEnabled(false);

  for (uint i = 0; i < npcs-1; ++i) {
    // e[i-1] != e[i]
    existEnabled |= (topo.pfmla_vbl(*topo.pcs[i].rvbls[0]) != topo.pfmla_vbl(*topo.pcs[i].rvbls[1]));
    // t[i-1] != t[i]
    tokenPFs[i] = (topo.pfmla_vbl(*topo.pcs[i].rvbls[2]) != topo.pfmla_vbl(*topo.pcs[i].rvbls[3]));
  }
  // e[N-2] == e[N-1]
  existEnabled |= (topo.pfmla_vbl(*topo.pcs[npcs-1].rvbls[0]) == topo.pfmla_vbl(*topo.pcs[npcs-1].rvbls[1]));
  // t[N-2] == t[N-1]
  tokenPFs[npcs-1] = (topo.pfmla_vbl(*topo.pcs[npcs-1].rvbls[2]) == topo.pfmla_vbl(*topo.pcs[npcs-1].rvbls[3]));

  sys.invariant = (SingleTokenPF(tokenPFs) & existEnabled);
}

/** Dijkstra's two bit token "spring".**/
  void
InstTwoBitTokenSpring(Xn::Sys& sys, uint npcs)
{
  if (npcs < 2) {
    DBog1( "Not enough processes (%u), need at least 2.", npcs );
    exit(1);
  }

  Xn::Net& topo = sys.topology;

  topo.add_variables("x", npcs, 2);
  topo.add_variables("up", npcs, 2);

  topo.add_processes("Bot", 1);
  topo.add_processes("P", npcs-2);
  topo.add_processes("Top", 1);

  // Make this f(i) = i
  Xn::NatMap indices(npcs-2);
  for (uint i = 0; i < npcs-2; ++i) {
    indices.membs[i] = (int)i;
  }
  indices.expression_chunks.push("");
  // P process reads x[i-1]
  topo.add_read_access(&topo.pc_symms[1], &topo.vbl_symms[0], indices);

  // Make this f(i) = i+1
  indices = Xn::NatMap(npcs-2);
  for (uint i = 0; i < npcs-2; ++i) {
    indices.membs[i] = (int)i+1;
  }
  indices.expression_chunks.push("+1");
  // P process writes x[i] and up[i]
  topo.add_write_access(&topo.pc_symms[1], &topo.vbl_symms[0], indices);
  topo.add_write_access(&topo.pc_symms[1], &topo.vbl_symms[1], indices);

  // Make this f(i) = i+2
  indices = Xn::NatMap(npcs-2);
  for (uint i = 0; i < npcs-2; ++i) {
    indices.membs[i] = (int)i+2;
  }
  indices.expression_chunks.push("+2");
  // P process reads x[i+1] and up[i+1]
  topo.add_read_access(&topo.pc_symms[1], &topo.vbl_symms[0], indices);
  topo.add_read_access(&topo.pc_symms[1], &topo.vbl_symms[1], indices);

  indices = Xn::NatMap(1);

  // Top process reads x[N-2]
  indices.membs[0] = (int)npcs-2;
  indices.expression_chunks[0] = indices.membs[0];
  topo.add_read_access(&topo.pc_symms[2], &topo.vbl_symms[0], indices);

  // Bot process writes x[0] and up[0]
  indices.membs[0] = (int)0;
  indices.expression_chunks[0] = indices.membs[0];
  topo.add_write_access(&topo.pc_symms[0], &topo.vbl_symms[0], indices);
  topo.add_write_access(&topo.pc_symms[0], &topo.vbl_symms[1], indices);

  // Top process writes x[N-1] and up[N-1]
  indices.membs[0] = (int)npcs-1;
  indices.expression_chunks[0] = indices.membs[0];
  topo.add_write_access(&topo.pc_symms[2], &topo.vbl_symms[0], indices);
  topo.add_write_access(&topo.pc_symms[2], &topo.vbl_symms[1], indices);

  // Bot process reads x[1] and up[1]
  indices.membs[0] = (int)1;
  indices.expression_chunks[0] = indices.membs[0];
  topo.add_read_access(&topo.pc_symms[0], &topo.vbl_symms[0], indices);
  topo.add_read_access(&topo.pc_symms[0], &topo.vbl_symms[1], indices);


  // Commit to using this topology, and initilize MDD stuff
  sys.commit_initialization();
  sys.synLegit = true;
  sys.liveLegit = true;

  // Formulas for each process having a token.
  vector<PF> tokenPFs(npcs);
  // ((x[0] == x[1]) &&
  //  (up[1] == 0))
  tokenPFs[0] = ((topo.pfmla_vbl(*topo.vbl_symms[0].membs[0]) == topo.pfmla_vbl(*topo.vbl_symms[0].membs[1])) &&
                 (topo.pfmla_vbl(*topo.vbl_symms[1].membs[1]) == 0));
  for (uint i = 1; i < npcs-1; ++i) {
      // ((x[i] != x[i-1])
      //  ||
      //  ((x[i] == x[i+1]) &&
      //  (up[i] == 1) &&
      //  (up[i+1] == 0)))
      tokenPFs[i] =
        ((topo.pfmla_vbl(*topo.vbl_symms[0].membs[i])
          != topo.pfmla_vbl(*topo.vbl_symms[0].membs[i-1]))
         ||
         ((topo.pfmla_vbl(*topo.vbl_symms[0].membs[i])
           == topo.pfmla_vbl(*topo.vbl_symms[0].membs[i+1]))
          &&
          (topo.pfmla_vbl(*topo.vbl_symms[1].membs[i]) == 1) &&
          (topo.pfmla_vbl(*topo.vbl_symms[1].membs[i+1]) == 0)));
  }
  // (x[N-1] != x[N-2])
  tokenPFs[npcs-1] = (topo.pfmla_vbl(*topo.vbl_symms[0].membs[npcs-1]) !=
                      topo.pfmla_vbl(*topo.vbl_symms[0].membs[npcs-2]));

  // ((exactly_one_token) && (up[0] == 1) && (up[N-1] == 0))
  sys.invariant = (SingleTokenPF(tokenPFs) &
                   (topo.pfmla_vbl(*topo.vbl_symms[1].membs[0]) == 1) &
                   (topo.pfmla_vbl(*topo.vbl_symms[1].membs[npcs-1]) == 0));
}

#if 0

/** Testing token ring.
 * Only enforce that a subset of the invariant be closed.
 **/
  void
InstTestTokenRing(Xn::Sys& sys, uint npcs)
{
  //const uint domsz = 3;
  Xn::Net& topo = sys.topology;
  // Build a unidirectional ring where each process P_i.
  for (uint i = 0; i < npcs; ++i) {
    char name[10];
    XnPc& pc = Grow1(topo.pcs);

    sprintf(name, "x%u", i);
    pc.addVbl(XnVbl(name, 2));
    sys.markShadowVbl(i, pc.wvbls.size()-1);

    sprintf(name, "t%u", i);
    pc.addVbl(XnVbl(name, 2));
    pc.addPriv(decmod(i, 1, npcs), pc.wvbls.size()-1);

    sprintf(name, "e%u", i);
    pc.addVbl(XnVbl(name, 2));
    pc.addPriv(decmod(i, 1, npcs), pc.wvbls.size()-1);

    sprintf(name, "ready%u", i);
    pc.addVbl(XnVbl(name, 2));
  }

  // Commit to using this topology, and initilize MDD stuff
  sys.commitInitialization();

  // Set priorities.
  //for (uint pcIdx = 0; pcIdx < npcs; ++pcIdx) {
  //  sys.niceIdxFo(pcIdx, npcs-pcIdx-1);
  //}

  for (uint actId = 0; actId < topo.nPossibleActs(); ++actId)
  {
    const XnAct& act = topo.action(actId);
    bool add = false;
    uint t_me = act.w0[1];
    uint e_me = act.w0[2];
    uint r_me = act.w0[3];
    uint t_lo = act.r0[1];
    uint e_lo = act.r0[2];
    uint t_img = act.w1[1];
    uint e_img = act.w1[2];
    uint r_img = act.w1[3];

    if (act.pcIdx == 0) {
      if (e_me == e_lo && t_me != t_lo) {
        if (e_img != e_me && r_img == 0 && t_img == t_me) {
          //add = true;
        }
      }
      else if (e_me == e_lo && t_me == t_lo && t_me == 0 && r_me == 0)
      {
        if (e_img != e_me && r_img == 1 && t_img == t_me) {
          //add = true;
        }
      }
      else if (e_me == e_lo && t_me == t_lo && (t_me == 1 || r_me == 1))
      {
        if (e_img != e_me && t_img != t_me && r_img == 0) {
          //add = true;
        }
      }
    }
    else {
      if (e_me != e_lo && t_me == t_lo) {
        if (e_img != e_me && r_img == 0 && t_img == t_me) {
          //add = true;
        }
      }
      else if (e_me != e_lo && t_me != t_lo && t_me == 0 && r_me == 0)
      {
        if (e_img != e_me && r_img == 1 && t_img == t_me) {
          //add = true;
        }
      }
      else if (e_me != e_lo && t_me != t_lo && (t_me == 1 || r_me == 1))
      {
        if (e_img != e_me && t_img != t_me && r_img == 0) {
          //add = true;
        }
      }
    }
    if (add) {
      sys.actions.push_back(actId);
    }
  }

  // Formulas for each process having a token.
  vector<PF> tokenPFs(npcs);

  for (uint pcidx = 0; pcidx < npcs; ++pcidx) {
    const uint pcidx_p = decmod(pcidx, 1, npcs);
    Set< Cx::Tuple<uint,2> > vbls;
    vbls |= Cx::Tuple<uint,2>(pcidx, 0);
    vbls |= Cx::Tuple<uint,2>(pcidx_p, 0);

    if (pcidx == 0) {
      const Cx::PFmla& pf =
        (topo.pfVbl(pcidx, 0) == topo.pfVbl(pcidx_p, 0))
        & (topo.pfVblPrimed(pcidx, 0) != topo.pfVblPrimed(pcidx_p, 0));
      sys.addShadowAct(pf, vbls);
    }
    else {
      const Cx::PFmla& pf =
        (topo.pfVbl(pcidx, 0) != topo.pfVbl(pcidx_p, 0))
        & (topo.pfVblPrimed(pcidx, 0) == topo.pfVblPrimed(pcidx_p, 0));
      sys.addShadowAct(pf, vbls);
    }
  }


  // x[0] == x[N-1]
  tokenPFs[0] = (topo.pfVbl(0, 0) == topo.pfVbl(npcs-1, 0));
  for (uint pcIdx = 1; pcIdx < npcs; ++pcIdx) {
    // x[i] != x[i-1]
    tokenPFs[pcIdx] = (topo.pfVbl(pcIdx, 0) != topo.pfVbl(pcIdx-1, 0));
  }

  sys.invariant = (SingleTokenPF(tokenPFs));
}

/** Agreement.
 * Only enforce that a subset of the invariant be closed.
 **/
  void
InstAgreementRing(Xn::Sys& sys, uint npcs)
{
  Xn::Net& topo = sys.topology;
  // Build a bidirectional ring.
  for (uint i = 0; i < npcs; ++i) {
    char name[10];
    XnPc& pc = Grow1(topo.pcs);

    sprintf(name, "a%u", i);
    pc.addVbl(XnVbl(name, npcs));

    sprintf(name, "x%u", i);
    pc.addVbl(XnVbl(name, npcs));
    sys.markShadowVbl(i, pc.wvbls.size()-1);

    pc.addPriv(decmod(i, 1, npcs), 0);
    //pc.addPriv(incmod(i, 1, npcs), 0);
  }

  // Commit to using this topology, and initilize MDD stuff
  sys.commitInitialization();

  // Set priorities.
  for (uint pcIdx = 0; pcIdx < npcs; ++pcIdx) {
    sys.niceIdxFo(pcIdx, npcs-pcIdx-1);
  }

  sys.invariant = true;
  for (uint pcIdx = 1; pcIdx < npcs; ++pcIdx) {
    sys.invariant &= (topo.pfVbl(pcIdx, 1) == topo.pfVbl(pcIdx-1, 1));
  }
}
#endif

