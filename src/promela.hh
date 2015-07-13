
#ifndef PROMELA_HH_
#define PROMELA_HH_
#include "cx/synhax.hh"
namespace Cx {
  class OFile;
}
namespace Xn {
  class Net;
  class Sys;
}

void
OPutPromelaModel(Cx::OFile& ofile, const Xn::Sys& sys, const Xn::Net& otopology);

#endif

