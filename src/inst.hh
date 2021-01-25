
#ifndef INST_HH_
#define INST_HH_
#include "cx/synhax.hh"

#include "namespace.hh"

void
UnidirectionalRing(Xn::Net& topo, uint npcs, uint domsz,
                   const char* basename, bool symmetric, bool distinguished);
void
SilentShadowRing(Xn::Sys& sys, const uint npcs,
                 const char* puppet_vbl_name, const uint puppet_vbl_domsz,
                 const char* shadow_vbl_name, const uint shadow_vbl_domsz);
P::Fmla
SingleTokenPFmla(const vector<P::Fmla>& tokenPFs);
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

END_NAMESPACE
#endif

