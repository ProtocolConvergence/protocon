
#ifndef INST_HH_
#define INST_HH_
#include "cx/synhax.hh"

namespace Xn {
class Sys;
}

void
InstThreeColoringRing(Xn::Sys& sys, uint npcs);
void
InstTwoColoringRing(Xn::Sys& sys, uint npcs);
void
InstMatching(Xn::Sys& sys, uint npcs, bool symmetric = true);
void
InstSumNot(Xn::Sys& sys, uint npcs, uint domsz, uint target);
void
InstAgreementRing(Xn::Sys& sys, uint npcs);
void
InstDijkstraTokenRing(Xn::Sys& sys, uint npcs);
void
InstThreeBitTokenRing(Xn::Sys& sys, uint npcs);
void
InstTwoBitTokenSpring(Xn::Sys& sys, uint npcs);
#if 0
void
InstTestTokenRing(Xn::Sys& sys, uint npcs);
#endif

#endif

