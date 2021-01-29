
#include "kautz.hh"
#include "cx/ofile.hh"

static int
egcd(int* ret_a, int* ret_b);
static void
linear_congruence(Cx::Table<uint>& ans, uint a, uint n, uint b);
static void
gkautz_hood(Cx::Table<uint>& hood, uint vidx, uint degree, uint n);

  int
egcd(int* ret_a, int* ret_b)
{
  int a = *ret_a;
  int b = *ret_b;
  int x = 0;
  int y = 1;
  int u = 1;
  int v = 0;
  while (a != 0) {
    int q = b / a;
    int r = b % a;
    b = a;
    a = r;
    int m = x - u * q;
    x = u;
    u = m;
    int n = y - v * q;
    y = v;
    v = n;
  }
  *ret_a = x;
  *ret_b = y;
  return b;
}

/**
 * a x % n = b
 */
  void
linear_congruence(Cx::Table<uint>& ans, uint a, uint n, uint b)
{
  int r = a,
      s = n;
  uint d = umod_int(egcd(&r, &s), n);
  uint n_div_d = n / d;
  if (0 != b % d)  return;
  uint x0 = umod_int(r * (int) b / (int)d, n);
  for (uint i = 0; i < d; ++i) {
    ans.push((x0 + i * n_div_d) % n);
  }
}

/**
 * Generalized Kautz graph topology of degree {degree}.
 * The {hood} parameter is filled by 2*{degree} nodes.
 * The first {degree} nodes are sources for arcs whose destination node is {vidx}.
 * The second {degree} nodes are destinations for arcs whose source node is {vidx}.
 */
  void
gkautz_hood(Cx::Table<uint>& hood, uint vidx, uint degree, uint n)
{
  // For arcs ending at node {vidx}, solve the following
  //   -(vidx + q) % n = i * degree % n
  // for
  //   q <- {1,...,degree}
  // to obtain each source node {i}.
  // Depending on {degree} and {n}, a single {q} may generate zero or multiple solutions,
  // but there are exactly {degree} solutions in total.
  for (uint q = 1; q <= degree; ++q) {
    Cx::Table<uint> ans;
    linear_congruence
      (ans, degree, n,
       umod_int (- (int)(vidx + q), n)
      );
    for (uint i = 0; i < ans.sz(); ++i) {
      hood.push(ans[i]);
      //DBog3("%0.2u %0.2u %u", ans[i], vidx, q);
    }
  }
  Claim2( hood.sz() ,==, degree );

  // For arcs beginning at node {vidx}, solve the following
  //   j = -(vidx * degree + q) % n
  // for
  //   q <- {1,...,degree}
  // to obtain each destination node {j}.
  // Each q gives a unique {j}.
  for (uint q = 1; q <= degree; ++q) {
    uint j = umod_int (-(int)(vidx * degree + q), n);
    hood.push(j);
    //DBog3("%0.2u %0.2u %u", vidx, j, q);
  }
  Claim2( hood.sz() ,==, 2*degree );
}

/**
 * Generalized Kautz graph topology of degree {degree}.
 * The {hood} parameter is filled by {x_degree}+{o_degree} nodes.
 * The first {x_degree} nodes are sources for arcs whose destination node is {vidx},
 * excluding {vidx} and duplicate source nodes.
 * The second {o_degree} nodes are destinations for arcs whose source node is {vidx},
 * excluding {vidx} and duplicate destination nodes.
 *
 * \return  The indegree {x_degree} of this node.
 */
  uint
gkautz_comm_hood(Cx::Table<uint>& hood, uint vidx, uint degree, uint n)
{
  gkautz_hood(hood, vidx, degree, n);
  uint x_degree;
  uint off = 0;
  for (uint i = 0; i < degree; ++i) {
    bool found = (vidx == hood[i]);
    for (uint j = 0; j < off && !found; ++j) {
      if (hood[j] == hood[i])
        found = true;
    }
    if (!found)
      hood[off++] = hood[i];
  }
  x_degree = off;
  for (uint i = degree; i < 2*degree; ++i) {
    bool found = (vidx == hood[i]);
    for (uint j = x_degree; j < off && !found; ++j) {
      if (hood[j] == hood[i])
        found = true;
    }
    if (!found)
      hood[off++] = hood[i];
  }
  if (hood.sz() != off) {
    hood.resize(off);
  }
  return x_degree;
}

  void
oput_graphviz_kautz(Cx::OFile& ofile, uint degree, uint nverts)
{
  ofile
    << "digraph G {\n"
    << "overlap=scale;\n"
    << "splines=true;\n"
    ;

  for (uint i = 0; i < nverts; ++i) {
    Cx::Table<uint> xo_arcs;
    Cx::Table<uint> o_arcs;
    Cx::Table<uint> x_arcs;

    Cx::Table<uint> hood;
    uint x_degree = gkautz_comm_hood(hood, i, degree, nverts);
    for (uint j = 0; j < x_degree; ++j) {
      uint v = hood[j];
      if (v > i) {
        x_arcs << v;
      }
    }
    uint o_degree = hood.sz() - x_degree;
    for (uint j = 0; j < o_degree; ++j) {
      uint v = hood[x_degree + j];
      if (v > i) {
        if (x_arcs.elem_ck(v)) {
          x_arcs.remove(v);
          xo_arcs << v;
        }
        else {
          o_arcs << v;
        }
      }
    }
    for (uint j = 0; j < xo_arcs.sz(); ++j)
      ofile << i << " -> " << xo_arcs[j] << " [dir=\"both\"]\n";
    for (uint j = 0; j < x_arcs.sz(); ++j)
      ofile << x_arcs[j] << " -> " << i << "\n";
    for (uint j = 0; j < o_arcs.sz(); ++j)
      ofile << i << " -> " << o_arcs[j] << "\n";
  }
  ofile << "}\n";
}

