
#ifndef UDP_OFILE_HH_
#define UDP_OFILE_HH_

#include "cx/synhax.hh"

#include "namespace.hh"

void
oput_udp_include_file(std::ostream& ofile, const Xn::Sys& sys, const Xn::Net& o_topology);
void
oput_udp_file(std::ostream& ofile, const Xn::Sys& sys, const Xn::Net& o_topology);

END_NAMESPACE
#endif

