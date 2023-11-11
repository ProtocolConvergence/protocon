
#ifndef KAUTZ_HH_
#define KAUTZ_HH_

#include <fildesh/ostream.hh>

#include "cx/table.hh"

uint
gkautz_comm_hood(Cx::Table<uint>& hood, uint vidx, uint degree, uint n);
void
oput_graphviz_kautz(std::ostream& ofile, uint degree, uint nverts);

#endif

