
#ifndef GRAPHVIZ_HH_
#define GRAPHVIZ_HH_

#include "cx/ofile.hh"

namespace Xn {
  class Net;
}

void
oput_graphviz_file(Cx::OFile& of, const Xn::Net& topo);

#endif

