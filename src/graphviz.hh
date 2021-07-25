#ifndef GRAPHVIZ_HH_
#define GRAPHVIZ_HH_

#include <ostream>
#include "namespace.hh"

void
oput_graphviz_file(std::ostream& of, const Xn::Net& topo);

END_NAMESPACE
#endif
