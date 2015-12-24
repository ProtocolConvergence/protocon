
#include "graphviz.hh"
#include "xnsys.hh"

#include "namespace.hh"

  void
oput_graphviz_file(Cx::OFile& of, const Xn::Net& topo)
{
  of << "digraph G {\n"
    << " margin=0;\n"
    << " edge [weight=5];\n\n";

  Cx::Map< uint, Set<uint> > own_map;
  for (uint i = 0; i < topo.pcs.sz(); ++i) {
    const Xn::Pc& pc = topo.pcs[i];
    of << "  P" << i << " [label=\"" << name_of(pc) << "\"];\n";
    for (uint j = 0; j < pc.wvbls.sz(); ++j) {
      const Xn::Vbl& vbl = *pc.wvbls[j];
      own_map[vbl.pfmla_idx] << i;
    }
  }
  of << "\n";
  Cx::Map< uint, Set<uint> > pc_read_map;
  for (uint i = 0; i < topo.pcs.sz(); ++i) {
    const Xn::Pc& pc = topo.pcs[i];
    for (uint j = 0; j < pc.rvbls.sz(); ++j) {
      const Xn::Vbl& vbl = *pc.rvbls[j];
      const Set<uint>& pc_idcs = own_map[vbl.pfmla_idx];
      Set<uint>::const_iterator it;
      for (it = pc_idcs.begin(); it != pc_idcs.end(); ++it) {
        if (*it != i) {
          pc_read_map[*it] << i;
        }
      }
    }
  }
  for (uint i = 0; i < topo.pcs.sz(); ++i) {
    const Set<uint>& pc_idcs = pc_read_map[i];
    Set<uint>::const_iterator it;
    for (it = pc_idcs.begin(); it != pc_idcs.end(); ++it) {
      if (pc_read_map[*it].elem_ck(i)) {
        if (i < *it) {
          of << "  P" << i << " -> P" << *it << " [dir=\"both\"]\n";
        }
      }
      else {
        of << "  P" << i << " -> P" << *it << "\n";
      }
    }
  }
  of << "}\n";
}

END_NAMESPACE

