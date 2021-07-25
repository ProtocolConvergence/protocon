
#ifndef PROMELA_HH_
#define PROMELA_HH_
#include "cx/synhax.hh"

#include "namespace.hh"

void
OPutPromelaModel(std::ostream& ofile, const Xn::Sys& sys, const Xn::Net& otopology);

END_NAMESPACE
#endif

