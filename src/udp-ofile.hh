
#ifndef UDP_OFILE_HH_
#define UDP_OFILE_HH_

#include "cx/ofile.hh"

namespace Xn {
  class Net;
  class Sys;
}

void
oput_udp_file(Cx::OFile& ofile, const Xn::Sys& xsys, const Xn::Net& o_topology);

#endif

