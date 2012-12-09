
#ifndef INST_HH_
#define INST_HH_
#include "synhax.hh"

class XnSys;

void
ColorRing(XnSys& sys, uint npcs);
void
InstMatching(XnSys& sys, uint npcs);
void
InstDijkstraTokenRing(XnSys& sys, uint npcs);
void
InstThreeBitTokenRing(XnSys& sys, uint npcs);
void
InstTwoBitTokenSpring(XnSys& sys, uint npcs);

#endif

