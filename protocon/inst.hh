
#ifndef INST_HH_
#define INST_HH_
#include "synhax.hh"

class XnSys;

void
InstThreeColoringRing(XnSys& sys, uint npcs);
void
InstTwoColoringRing(XnSys& sys, uint npcs);
void
InstMatching(XnSys& sys, uint npcs);
void
InstSumNot(XnSys& sys, uint npcs, uint domsz, uint target);
void
InstDijkstraTokenRing(XnSys& sys, uint npcs);
void
InstThreeBitTokenRing(XnSys& sys, uint npcs);
void
InstTwoBitTokenSpring(XnSys& sys, uint npcs);

#endif

