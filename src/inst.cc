/**
 * \file inst.cc
 *
 * Functions to set up problem instances.
 */

#include "inst.hh"
#include "xnsys.hh"
#include <stdio.h>

#include "namespace.hh"

/** Create a unidirectional ring topology.**/
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
    Xn::PcSymm* pc_symm = topo.add_processes("P", "i", npcs);

    // Make this f(i) = i-1
    Xn::NatMap indices(npcs);
    for (uint i = 0; i < npcs; ++i) {
      indices.membs[i] = (int)i - 1;
    }
    indices.expression = "i-1";
    topo.add_access(pc_symm, vbl_symm, indices, Xn::ReadAccess);

    // Now make this f(i) = i
    indices = Xn::NatMap(npcs);
    for (uint i = 0; i < npcs; ++i) {
      indices.membs[i] = (int)i;
    }
    indices.expression = "i";
    topo.add_access(pc_symm, vbl_symm, indices, Xn::WriteAccess);
  }
  else {
    // Create a new symmetry for each process.
    for (uint i = 0; i < npcs; ++i) {
      Xn::PcSymm* pc_symm = topo.add_processes(
          "P" + std::to_string(i), "i", 1);

      // Make this f(j) = i-1
      Xn::NatMap indices(1);
      indices.membs[0] = (int)i - 1;
      indices.expression = std::to_string(indices.membs[0]);
      topo.add_access(pc_symm, vbl_symm, indices, Xn::ReadAccess);

      // Now make this f(j) = i
      indices.membs[0] = (int)i;
      indices.expression = std::to_string(indices.membs[0]);
      topo.add_access(pc_symm, vbl_symm, indices, Xn::WriteAccess);
    }
  }

  if (distinguished) {
    ++ npcs;

    Xn::PcSymm* pc_symm = topo.add_processes("Bot", "i", 1);

    Xn::NatMap indices(1);
    indices.membs[0] = (int)npcs - 2;
    indices.expression = std::to_string(indices.membs[0]);
    topo.add_access(pc_symm, vbl_symm, indices, Xn::ReadAccess);

    indices.membs[0] = (int)npcs - 1;
    indices.expression = std::to_string(indices.membs[0]);
    topo.add_access(pc_symm, vbl_symm, indices, Xn::WriteAccess);
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
    indices.expression = "i+1";
    topo.add_access(pc_symm, &topo.vbl_symms[0], indices, Xn::ReadAccess);
  }
  else {
    for (uint i = 0; i < npcs; ++i) {
      Xn::PcSymm* pc_symm = &topo.pc_symms[i];
      // Make this f(j) = i+1
      Xn::NatMap indices(1);
      indices.membs[0] = (int)i + 1;
      indices.expression = std::to_string(indices.membs[0]);
      topo.add_access(pc_symm, &topo.vbl_symms[0], indices, Xn::ReadAccess);
    }
  }
}

/** Create a bidirectional ring
 * with a "((future & silent) % puppet)" constraint.
 **/
  void
SilentShadowRing(Xn::Sys& sys, const uint npcs,
                 const char* puppet_vbl_name, const uint puppet_vbl_domsz,
                 const char* shadow_vbl_name, const uint shadow_vbl_domsz)
{
  Xn::Net& topo = sys.topology;
  topo.add_variables(puppet_vbl_name, npcs, puppet_vbl_domsz, Xn::Puppet);
  topo.add_variables(shadow_vbl_name, npcs, shadow_vbl_domsz, Xn::Shadow);
  Xn::PcSymm* pc_symm = topo.add_processes("P", "i", npcs);
  Xn::NatMap indices(npcs);

  for (uint i = 0; i < npcs; ++i)
    indices.membs[i] = (int)i - 1;
  indices.expression = "i-1";
  topo.add_access(pc_symm, &topo.vbl_symms[0], indices, Xn::ReadAccess);

  for (uint i = 0; i < npcs; ++i)
    indices.membs[i] = (int)i;
  indices.expression = "i";
  topo.add_access(pc_symm, &topo.vbl_symms[0], indices, Xn::WriteAccess);

  for (uint i = 0; i < npcs; ++i)
    indices.membs[i] = (int)i + 1;
  indices.expression = "i+1";
  topo.add_access(pc_symm, &topo.vbl_symms[0], indices, Xn::ReadAccess);

  for (uint i = 0; i < npcs; ++i)
    indices.membs[i] = (int)i;
  indices.expression = "i";
  topo.add_access(pc_symm, &topo.vbl_symms[1], indices, Xn::WriteAccess);

  sys.spec->invariant_style = Xn::FutureAndShadow;
  sys.spec->invariant_scope = Xn::ShadowInvariant;
  sys.commit_initialization();
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
    const PFmlaVbl m_p = topo.pfmla_vbl (*pc.rvbls[0]);
    const PFmlaVbl m_r = topo.pfmla_vbl (*pc.rvbls[1]);
    const PFmlaVbl m_s = topo.pfmla_vbl (*pc.rvbls[2]);

    sys.invariant &= (m_p != m_r) && (m_r != m_s);
  }
}


/**
 * Return the states for which only one process has a token.
 * \param tokenPFs  Formulas for each process having a token.
 */
  P::Fmla
SingleTokenPFmla(const vector<P::Fmla>& tokenPFs)
{
  const uint n = tokenPFs.size();
  vector<P::Fmla> singleToken(n, P::Fmla(true));
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

  P::Fmla pf( false );
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
    const PFmlaVbl c_p = topo.pfmla_vbl(decmod(i, 1, npcs));
    const PFmlaVbl c_r = topo.pfmla_vbl(i);
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
    const PFmlaVbl x_p = topo.pfmla_vbl (*pc.rvbls[0]);
    const PFmlaVbl x_r = topo.pfmla_vbl (*pc.rvbls[1]);
    const PFmlaVbl x_s = topo.pfmla_vbl (*pc.rvbls[2]);

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
    const PFmlaVbl x_p = topo.pfmla_vbl (*pc.rvbls[0]);
    const PFmlaVbl x_r = topo.pfmla_vbl (*pc.rvbls[1]);

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
    const PFmlaVbl x_p = topo.pfmla_vbl (*pc.rvbls[0]);
    const PFmlaVbl x_r = topo.pfmla_vbl (*pc.rvbls[1]);
    const PFmlaVbl x_s = topo.pfmla_vbl (*pc.rvbls[2]);

    sys.invariant &= (((x_r - x_p) % npcs) == ((x_s - x_r) % npcs));
  }
}

END_NAMESPACE

