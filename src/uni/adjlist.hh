#ifndef AdjList_HH_
#define AdjList_HH_

#include "cx/table.hh"

#define DoTwice( stmt ) \
  for (uint DoTwice_Index = 0; \
       DoTwice_Index < 2; \
       DoTwice_Index = DoTwice_Index==0 ? (stmt), 1 : 2)

#include "../namespace.hh"
template <typename T>
class AdjList {
private:
  struct Node {
    zuint offset; ///< Offset for the outgoing arc list.
    zuint degree; ///< Outdegree of the node.

    Node() : offset(SIZE_MAX), degree(0) {}
    zuint endidx() const { return offset + degree; }
  };

  Table<Node> nodes;
  Table<T> arcs;

public:
  AdjList(zuint nnodes);

  void increment_degree(zuint id, zuint n=1) {
    nodes[id].degree += n;
  }
  void increment_degrees(zuint n=1) {
    for (uint i = 0; i < nodes.sz(); ++i) {
      increment_degree(i, n);
    }
  }
  void commit_degrees();

  void flush() {
    for (uint i = 0; i < nodes.sz(); ++i) {
      nodes[i].degree = 0;
    }
  }

  zuint nnodes() const {
    return nodes.sz();
  }

  zuint degree(zuint id) const {
    return nodes[id].degree;
  }

  const T* arcs_from(zuint src) const {
    return &arcs[nodes[src].offset];
  }

  const T& arc_from(zuint src, zuint i) const {
    return arcs[nodes[src].offset + i];
  }

  void del_arcs_from(zuint src) {
    nodes[src].degree = 0;
  }

  void add_arc(zuint src, const T& dst);
  void del_arc(zuint src, const T& dst);
};

template <typename T>
AdjList<T>::AdjList(zuint nnodes)
{
  nodes.affysz(nnodes);

  if (nnodes == 0)
    return;

  nodes[0].offset = SIZE_MAX;
}

template <typename T>
  void
AdjList<T>::commit_degrees()
{
  // Nothing to initialize.
  if (nnodes() == 0)
    return;

  Claim( nodes[0].offset == SIZE_MAX );
  nodes[0].offset = 0;

  for (zuint i = 1; i < nnodes(); ++i) {
    nodes[i].offset = nodes[i-1].endidx();
    nodes[i-1].degree = 0;
  }

  arcs.affysz(nodes.top().endidx());
  nodes[nnodes()-1].degree = 0;
}

template <typename T>
  void
AdjList<T>::add_arc(zuint src, const T& dst)
{
  if (nodes[0].offset != SIZE_MAX) {
    arcs[nodes[src].endidx()] = dst;
  }
  nodes[src].degree += 1;
}

template <typename T>
  void
AdjList<T>::del_arc(zuint src, const T& dst)
{
  const zuint begidx = nodes[src].offset;
  const zuint endidx = nodes[src].endidx();
  zuint n = 0;
  for (zuint i = begidx; i < endidx; ++i) {
    if (arcs[i] == dst) {
      nodes[src].degree -= 1;
      n += 1;
    }
    else if (n > 0) {
      arcs[i-n] = arcs[i];
    }
  }
}
END_NAMESPACE
#endif
