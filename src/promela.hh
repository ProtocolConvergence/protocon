
#ifndef PROMELA_HH_
#define PROMELA_HH_
#include "cx/synhax.hh"
namespace Xn {
  class Net;
  class Sys;
}

void
OPutPromelaModel(ostream& of, const Xn::Sys& sys, const Xn::Net& topo);

#endif

