
#include "graphviz.hh"
#include "xnsys.hh"

#include "namespace.hh"

  void
oput_graphviz_file(std::ostream& of, const Xn::Net& topo)
{
  of << "digraph G {\n"
    << " margin=0;\n"
    << " edge [weight=5];\n\n";

  Cx::Map< unsigned, Set<unsigned> > own_map;
  for (unsigned i = 0; i < topo.pcs.sz(); ++i) {
    const Xn::Pc& pc = topo.pcs[i];
    of << "  P" << i << " [label=\"" << name_of(pc) << "\"];\n";
    for (unsigned j = 0; j < pc.wvbls.sz(); ++j) {
      const Xn::Vbl& vbl = *pc.wvbls[j];
      own_map[vbl.pfmla_idx] << i;
    }
  }
  of << "\n";
  Cx::Map< unsigned, Set<unsigned> > pc_read_map;
  for (unsigned i = 0; i < topo.pcs.sz(); ++i) {
    const Xn::Pc& pc = topo.pcs[i];
    for (unsigned j = 0; j < pc.rvbls.sz(); ++j) {
      const Xn::Vbl& vbl = *pc.rvbls[j];
      const Set<unsigned>& pc_idcs = own_map[vbl.pfmla_idx];
      Set<unsigned>::const_iterator it;
      for (it = pc_idcs.begin(); it != pc_idcs.end(); ++it) {
        if (*it != i) {
          pc_read_map[*it] << i;
        }
      }
    }
  }
  for (unsigned i = 0; i < topo.pcs.sz(); ++i) {
    const Set<unsigned>& pc_idcs = pc_read_map[i];
    Set<unsigned>::const_iterator it;
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

