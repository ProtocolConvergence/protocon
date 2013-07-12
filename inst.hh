
#ifndef INST_HH_
#define INST_HH_
#include "cx/synhax.hh"

namespace Cx {
  class PFmla;
}
namespace Xn {
class Net;
class Sys;
}

void
UnidirectionalRing(Xn::Net& topo, uint npcs, uint domsz,
                   const char* basename, bool symmetric, bool distinguished);
Cx::PFmla
SingleTokenPFmla(const vector<Cx::PFmla>& tokenPFs);
void
InstThreeColoringRing(Xn::Sys& sys, uint npcs);
void
InstTwoColoringRing(Xn::Sys& sys, uint npcs);
void
InstMatching(Xn::Sys& sys, uint npcs, bool symmetric = true);
void
InstSumNot(Xn::Sys& sys, uint npcs, uint domsz, uint target,
           const char* vbl_name = "x");
void
InstAgreementRing(Xn::Sys& sys, uint npcs, const char* vbl_name = "x");

#endif

