#ifndef SATSYN_INSTANCE_H_
#define SATSYN_INSTANCE_H_
#if defined(__cplusplus)
extern "C" {
#endif

#include "xnsys.h"

enum XnSysInstance {
    Sat3Inst,
    Sat3RingInst,
    Sat3RingWSatInst,
    MatchingInst,
    ColoringInst,
    TokenRing3BitInst,
    TokenRingDijkstraInst,
    TokenRingDijkstra4StateInst,
    NXnSysInstances
};

typedef enum XnSysInstance XnSysInstance;

XnSys
inst_coloring_XnSys(unsigned npcs, unsigned domsz);
XnSys
inst_matching_XnSys(unsigned npcs);
XnSys
inst_bit3_XnSys (unsigned npcs);
XnSys
inst_dijkstra_XnSys(unsigned npcs);
XnSys
inst_dijkstra4state_XnSys(unsigned npcs);

static inline
  unsigned
inc1mod(unsigned i, unsigned n)
{
  return (i + 1) % n;
}

static inline
  unsigned
dec1mod(unsigned i, unsigned n)
{
  return (i + n - 1) % n;
}


#if defined(__cplusplus)
}
#endif
#endif  /* #ifndef SATSYN_INSTANCE_H_ */
