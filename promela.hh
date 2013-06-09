
#ifndef PROMELA_HH_
#define PROMELA_HH_
#include "cx/synhax.hh"
namespace Xn {
  class Sys;
}

void
OPutPromelaModel(ostream& of, const Xn::Sys& sys);

#endif

