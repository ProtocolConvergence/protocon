/**
 * \file inst.cc
 *
 * Functions to set up problem instances.
 */

/** Increment followed by modulo.**/
  uint
incmod(uint i, uint by, uint n)
{
  return (i + by) % n;
}

/** Decrement followed by modulo.**/
  uint
decmod(uint i, uint by, uint n)
{
  return (i + n - (by % n)) % n;
}

/** Create a bidirectional ring topology.
 */
  void
BidirectionalRing(XnNet& topo, uint npcs, uint domsz)
{
  // Build a bidirectional ring where each process P_i
  // has variable m_i of domain size 3.
  for (uint i = 0; i < npcs; ++i) {
    char name[10];
    sprintf(name, "m%u", i);

    XnPc& pc = Grow1(topo.pcs);
    pc.addVbl(XnVbl(name, domsz));
    pc.addPriv(decmod(i, 1, npcs), 0);
    pc.addPriv(incmod(i, 1, npcs), 0);
  }
}

  void
UnidirectionalRing(XnNet& topo, uint npcs, uint domsz)
{
  // Build a bidirectional ring where each process P_i
  // has variable m_i of domain size 3.
  for (uint i = 0; i < npcs; ++i) {
    char name[10];
    sprintf(name, "m%u", i);

    XnPc& pc = Grow1(topo.pcs);
    pc.addVbl(XnVbl(name, domsz));
    pc.addPriv(decmod(i, 1, npcs), 0);
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
ColorRing(XnSys& sys, uint npcs)
{
  // Initializes the system as a bidirectional ring with a 3 value domain
  // and the topology defined in sys
  XnNet& topo=sys.topology;
  BidirectionalRing(topo,npcs,3);

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
  BidirectionalRing(topo, npcs, 3);

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

  void
InstDijkstraTokenRing(XnSys& sys, uint npcs)
{
  XnNet& topo = sys.topology;
  UnidirectionalRing(topo, npcs, npcs+1);

  // Commit to using this topology, and initilize MDD stuff
  topo.commitInitialization();
  sys.synLegit = true;
  sys.liveLegit = true;

  // Build an array of formulas which require exactly one process has a token.
  vector<PF> singleToken(npcs, PF(true));
  for (uint pcIdx = 0; pcIdx < npcs; ++pcIdx) {
    PF tokenPF;  // Formula for this process having a token.
    if (pcIdx == 0) {
      tokenPF = (topo.pfVbl(pcIdx, 0) == topo.pfVblR(pcIdx, 0));
    }
    else {
      tokenPF = (topo.pfVbl(pcIdx, 0) != topo.pfVblR(pcIdx, 0));
    }

    for (uint j = 0; j < npcs; ++j) {
      if (j == pcIdx) {
        // Process pcIdx has the only token
        // in the /singleToken[j]/ formula.
        singleToken[j] &= tokenPF; 
      }
      else {
        // Process pcIdx does not have a token
        // in the /singleToken[j]/ formula.
        singleToken[j] -= tokenPF; 
      }
    }
  }

  sys.invariant = false;
  for (uint pcIdx = 0; pcIdx < npcs; ++pcIdx) {
    sys.invariant |= singleToken[pcIdx];
  }
}

/** Three bit token ring.**/
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

  // Build an array of formulas which require exactly one process has a token.
  vector<PF> singleToken(npcs, PF(true));
  PF existEnabled(false);

  for (uint pcIdx = 0; pcIdx < npcs; ++pcIdx) {
    if (pcIdx == 0) {
      // e_i == e_{i-1}
      existEnabled |= (topo.pfVbl(pcIdx, 0) == topo.pfVblR(pcIdx, 0));
    }
    else {
      // e_i != e_{i-1}
      existEnabled |= (topo.pfVbl(pcIdx, 0) != topo.pfVblR(pcIdx, 0));
    }

    PF tokenPF;  // Formula for this process having a token.
    if (pcIdx == 0) {
      // t_{i-1} == t_i
      tokenPF = (topo.pfVbl(pcIdx, 1) == topo.pfVblR(pcIdx, 1));
    }
    else {
      // t_{i-1} != t_i
      tokenPF = (topo.pfVbl(pcIdx, 1) != topo.pfVblR(pcIdx, 1));
    }

    for (uint j = 0; j < npcs; ++j) {
      if (j == pcIdx) {
        // Process pcIdx has the only token
        // in the /singleToken[j]/ formula.
        singleToken[j] &= tokenPF; 
      }
      else {
        // Process pcIdx does not have a token
        // in the /singleToken[j]/ formula.
        singleToken[j] -= tokenPF; 
      }
    }
  }

  sys.invariant = false;
  for (uint pcIdx = 0; pcIdx < npcs; ++pcIdx) {
    sys.invariant |= singleToken[pcIdx];
  }
  sys.invariant &= existEnabled;
}

