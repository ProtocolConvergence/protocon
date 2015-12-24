
#ifndef GRAPHVIZ_HH_
#define GRAPHVIZ_HH_

#include "cx/ofile.hh"

#include "namespace.hh"

void
oput_graphviz_file(Cx::OFile& of, const Xn::Net& topo);

END_NAMESPACE
#endif

