
#ifndef KAUTZ_HH_
#define KAUTZ_HH_

#include "cx/synhax.hh"
#include "cx/table.hh"

namespace Cx {
  class OFile;
}

uint
gkautz_comm_hood(Cx::Table<uint>& hood, uint vidx, uint degree, uint n);
void
oput_graphviz_kautz(Cx::OFile& ofile, uint degree, uint nverts);

#endif

