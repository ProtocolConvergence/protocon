/**
 * \file inst.cc
 *
 * Functions to set up problem instances.
 */

#include "inst.hh"
#include "xnsys.hh"

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
UnidirectionalRing(XnNet& topo, uint npcs, uint domsz, const char* basename)
{
  // Build a bidirectional ring where each process P_i
  // has variable m_i of domain size 3.
  for (uint i = 0; i < npcs; ++i) {
    char name[10];
    sprintf(name, "%s%u", basename, i);

    XnPc& pc = Grow1(topo.pcs);
    pc.addVbl(XnVbl(name, domsz));
    pc.addPriv(decmod(i, 1, npcs), 0);
  }
}

/** Create a bidirectional ring topology.
 **/
static
  void
BidirectionalRing(XnNet& topo, uint npcs, uint domsz, const char* basename)
{
  // Build a bidirectional ring where each process P_i
  // has variable m_i of domain size 3.
  for (uint i = 0; i < npcs; ++i) {
    char name[10];
    sprintf(name, "%s%u", basename, i);

    XnPc& pc = Grow1(topo.pcs);
    pc.addVbl(XnVbl(name, domsz));
    pc.addPriv(decmod(i, 1, npcs), 0);
    pc.addPriv(incmod(i, 1, npcs), 0);
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
 * Performs the 3 color on a ring problem.  Each process must be assigned
 * a color such that it'd color is not the same as either of its
 * neighbors.  The domain is [0,2], corresponding to each of 3 arbitrary
 * colors.
 *
 * \param sys  The system context
 * \param npcs The number of processes
 */
  void
ColorRing(XnSys& sys, uint npcs)
{
  // Initializes the system as a bidirectional ring with a 3 value domain
  // and the topology defined in sys
  XnNet& topo=sys.topology;
  BidirectionalRing(topo,npcs,3,"c");

  // Commit to using this topology, and initilize MDD stuff
  topo.commitInitialization();
  sys.invariant=true;

  for(uint pcidx=0; pcidx<npcs; pcidx++){

    // mq is the current process, mp is the left process,
    // and mr is the right process.
    const PFVbl mp=topo.pfVblR(pcidx,0);
    const PFVbl mq=topo.pfVbl (pcidx,0);
    const PFVbl mr=topo.pfVblR(pcidx,1);

    // Add to the accepting states all of the states where
    // mq is a different color than both mp and mr
    sys.invariant &= (mp!=mq) && (mq!=mr);
  }
}

  void
InstMatching(XnSys& sys, uint npcs)
{
  XnNet& topo = sys.topology;
  BidirectionalRing(topo, npcs, 3, "m");

  // Commit to using this topology.
  // MDD stuff is initialized.
  topo.commitInitialization();
  sys.invariant = true;

  for (uint pcidx = 0; pcidx < npcs; ++pcidx) {
    const PFVbl mp = topo.pfVblR(pcidx, 0);
    const PFVbl mq = topo.pfVbl (pcidx, 0);
    const PFVbl mr = topo.pfVblR(pcidx, 1);

    // 0 = Self, 1 = Left, 2 = Right
    sys.invariant &=
      (mp == 1 && mq == 0 && mr == 2) || // ( left,  self, right)
      (mp == 2 && mq == 1           ) || // (right,  left,     X)
      (           mq == 2 && mr == 1);   // (    X, right,  left)
  }
}

/** Dijkstra's original token ring
 * with each process's variable with a domain of size N+1.
 **/
  void
InstDijkstraTokenRing(XnSys& sys, uint npcs)
{
  XnNet& topo = sys.topology;
  UnidirectionalRing(topo, npcs, npcs+1, "x");

  // Commit to using this topology, and initilize MDD stuff
  topo.commitInitialization();
  sys.synLegit = true;
  sys.liveLegit = true;

  // Formulas for each process having a token.
  vector<PF> tokenPFs(npcs);
  // (x[0] == x[N-1])
  tokenPFs[0] = (topo.pfVbl(0, 0) == topo.pfVblR(0, 0));
  for (uint pcIdx = 1; pcIdx < npcs; ++pcIdx) {
    // (x[i] == x[i-1])
    tokenPFs[pcIdx] = (topo.pfVbl(pcIdx, 0) != topo.pfVblR(pcIdx, 0));
  }
  sys.invariant = SingleTokenPF(tokenPFs);
}

/** Gouda's three bit token ring.**/
  void
InstThreeBitTokenRing(XnSys& sys, uint npcs)
{
  XnNet& topo = sys.topology;
  // Build a bidirectional ring where each process P_i
  // has variable m_i of domain size 3.
  for (uint i = 0; i < npcs; ++i) {
    char name[10];
    XnPc& pc = Grow1(topo.pcs);

    sprintf(name, "e%u", i);
    pc.addVbl(XnVbl(name, 2));
    sprintf(name, "t%u", i);
    pc.addVbl(XnVbl(name, 2));
    sprintf(name, "ready%u", i);
    pc.addVbl(XnVbl(name, 2));

    pc.addPriv(decmod(i, 1, npcs), 0);
    pc.addPriv(decmod(i, 1, npcs), 1);
  }

  // Commit to using this topology, and initilize MDD stuff
  topo.commitInitialization();
  sys.synLegit = true;
  sys.liveLegit = true;

  // Formulas for each process having a token.
  vector<PF> tokenPFs(npcs);
  // Formula for existence of an enabled process.
  PF existEnabled(false);

  // e[0] == e[N-1]
  existEnabled |= (topo.pfVbl(0, 0) == topo.pfVblR(0, 0));
  // t_{i-1} == t_i
  tokenPFs[0] = (topo.pfVbl(0, 1) == topo.pfVblR(0, 1));

  for (uint pcIdx = 1; pcIdx < npcs; ++pcIdx) {
    // e_i != e_{i-1}
    existEnabled |= (topo.pfVbl(pcIdx, 0) != topo.pfVblR(pcIdx, 0));
    // t_{i-1} != t_i
    tokenPFs[pcIdx] = (topo.pfVbl(pcIdx, 1) != topo.pfVblR(pcIdx, 1));
  }

  sys.invariant = (SingleTokenPF(tokenPFs) & existEnabled);
}

/** Dijkstra's two bit token "spring".**/
  void
InstTwoBitTokenSpring(XnSys& sys, uint npcs)
{
  if (npcs < 2) {
    DBog1( "Not enough processes (%u), need at least 2.", npcs );
    exit(1);
  }

  XnNet& topo = sys.topology;
  // Build a bidirectional ring where each process P_i
  // has variable m_i of domain size 3.
  for (uint i = 0; i < npcs; ++i) {
    char name[10];
    XnPc& pc = Grow1(topo.pcs);

    sprintf(name, "x%u", i);
    pc.addVbl(XnVbl(name, 2));
    sprintf(name, "up%u", i);
    pc.addVbl(XnVbl(name, 2));

    if (i > 0) {
      pc.addPriv(i-1, 0);
    }
    if (i < npcs-1) {
      pc.addPriv(i+1, 0);
      pc.addPriv(i+1, 1);
    }
  }
  // Commit to using this topology, and initilize MDD stuff
  topo.commitInitialization();
  sys.synLegit = true;
  sys.liveLegit = true;

  // Formulas for each process having a token.
  vector<PF> tokenPFs(npcs);
  // ((x[0] == x[1]) &&
  //  (up[1] == 0))
  tokenPFs[0] = ((topo.pfVbl(0, 0) == topo.pfVbl(1, 0)) &&
                 (topo.pfVbl(1, 1) == 0));
  for (uint pcIdx = 1; pcIdx < npcs-1; ++pcIdx) {
      // ((x[i] != x[i-1])
      //  ||
      //  ((x[i] == x[i+1]) &&
      //  (up[i] == 1) &&
      //  (up[i+1] == 0)))
      tokenPFs[pcIdx] =
        ((topo.pfVbl(pcIdx, 0) != topo.pfVbl(pcIdx-1, 0))
         ||
         ((topo.pfVbl(pcIdx, 0) == topo.pfVbl(pcIdx+1, 0)) &&
          (topo.pfVbl(pcIdx, 1) == 1) &&
          (topo.pfVbl(pcIdx+1, 1) == 0)));
  }
  // (x[N-1] != x[N-2])
  tokenPFs[npcs-1] = (topo.pfVbl(npcs-1, 0) != topo.pfVbl(npcs-2, 0));

  // ((exactly_one_token) && (up[0] == 1) && (up[N-1] == 0))
  sys.invariant = (SingleTokenPF(tokenPFs) &
                   (topo.pfVbl(0, 1) == 1) &
                   (topo.pfVbl(npcs-1, 1) == 0));
}

