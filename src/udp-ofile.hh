
#ifndef UDP_OFILE_HH_
#define UDP_OFILE_HH_

#include "cx/ofile.hh"

namespace Xn {
  class Sys;
}

void
oput_udp_file(Cx::OFile& ofile, const Xn::Sys& sys);

#endif

