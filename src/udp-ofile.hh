
#ifndef UDP_OFILE_HH_
#define UDP_OFILE_HH_

#include "cx/ofile.hh"

#include "namespace.hh"

void
oput_udp_include_file(OFile& ofile, const Xn::Sys& sys, const Xn::Net& o_topology);
void
oput_udp_file(OFile& ofile, const Xn::Sys& sys, const Xn::Net& o_topology);

END_NAMESPACE
#endif

