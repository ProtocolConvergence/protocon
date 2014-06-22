
extern "C" {
#include "cx/syscx.h"
#include "cx/bittable.h"
}

#include <algorithm>
#include "cx/fileb.hh"
#include "cx/map.hh"
#include "cx/table.hh"
#include "cx/bittable.hh"
#include "cx/set.hh"
#include "tuple.hh"

//#define UseBlissLib

#ifdef UseBlissLib
#include <graph.hh>
#endif

#ifdef UseBlissLib
#define UseBitTableDB
#endif


class LocalConfig
{
public:
  uint x_id;
  uint x_pd;
  uint x_sc;
  uint sc_cont_idx;
};

class LocalCont
{
public:
  uint x_id;
  uint x_sc;
  Cx::Table<uint> sc_configs;
};

class LocalVal
{
public:
  Cx::Table<uint> configs;
};

class LocalLegit
{
public:
  Cx::Table<LocalConfig> configs;
  Cx::Table<LocalCont> conts;
  Cx::Table<LocalVal> vals;
  Cx::Map<Cx::Tuple<uint,2>, uint> cont_map;

  explicit LocalLegit(uint domsz)
    : vals(domsz)
  {}
};

class FlatDigraph
{
private:
  uint* data;

  uint data_sz() const {
    const uint nnodes = this->nnodes();
    return 1 + data[nnodes-1] + (*this)[nnodes-1].sz();
  }
public:
  class Vertex
  {
    private:
      uint* data;
    public:
      explicit Vertex(uint* _data) : data(_data) {}

      uint sz() const {
        return data[-1];
      }
      uint operator[](uint i) const {
        return data[i];
      }
      uint& operator[](uint i) {
        return data[i];
      }
      uint* begin() {
        return &data[0];
      }
      uint* end() {
        return &data[data[-1]];
      }
  };

  FlatDigraph() : data(0) {}

  FlatDigraph(const Cx::Table< Cx::Table<uint> >& graph)
    : data(0)
  {
    *this = graph;
  }

  FlatDigraph(const FlatDigraph& graph)
    : data(0)
  {
    *this = graph;
  }

  ~FlatDigraph()
  {
    if (data) {
      data = &data[-1];
      delete[] data;
    }
  }

  FlatDigraph& operator=(const Cx::Table< Cx::Table<uint> >& graph)
  {
    if (data) {
      data = &data[-1];
      delete[] data;
    }
    const uint nnodes = graph.sz();
    uint narcs = 0;
    for (uint i = 0; i < nnodes; ++i) {
      narcs += graph[i].sz();
    }
    data = new uint[1 + 2*nnodes + narcs];
    data = &data[1];
    data[-1] = nnodes;
    if (nnodes > 0) {
      data[0] = 1+nnodes;
      data[data[0]-1] = graph[0].sz();
    }
    for (uint i = 1; i < nnodes; ++i) {
      data[i] = data[i-1] + data[data[i-1]-1] + 1;
      data[data[i]-1] = graph[i].sz();
    }
    for (uint i = 0; i < nnodes; ++i) {
      for (uint j = 0; j < (*this)[i].sz(); ++j) {
        (*this)[i][j] = graph[i][j];
      }
    }

    for (uint i = 0; i < nnodes; ++i) {
      std::sort ((*this)[i].begin(), (*this)[i].end());
    }
    return *this;
  }

  FlatDigraph& operator=(const FlatDigraph& graph)
  {
    if (data) {
      data = &data[-1];
      delete[] data;
    }
    const uint data_sz = graph.data_sz();
    data = new uint[data_sz];
    data = &data[1];

    RepliT( uint, &data[-1], &graph.data[-1], data_sz );
    return *this;
  }

  const Vertex operator[](uint v) const {
    return Vertex(&data[data[v]]);
  }

  Vertex operator[](uint v) {
    return Vertex(&data[data[v]]);
  }

  uint nnodes() const {
    return data[-1];
  }
  uint narcs() const {
    return data_sz() - 1 - 2*this->nnodes();
  }

  Sign cmp(const FlatDigraph& b) const
  {
    const FlatDigraph& a = *this;
    const uint a_data_sz = a.data_sz();
    const uint b_data_sz = b.data_sz();
    if (a_data_sz < b_data_sz) return -1;
    if (b_data_sz < a_data_sz) return  1;
    int ret = memcmp (&a.data[-1], &b.data[-1], a_data_sz * sizeof(uint));
    if (ret < 0)  return -1;
    if (ret > 0)  return  1;
    return 0;
  }

  bool operator==(const FlatDigraph& b) const {
    return (this->cmp(b) == 0);
  }
  bool operator!=(const FlatDigraph& b) const {
    return !(*this == b);
  }
  bool operator<=(const FlatDigraph& b) const {
    return (this->cmp(b) <= 0);
  }
  bool operator<(const FlatDigraph& b) const {
    return (this->cmp(b) < 0);
  }
  bool operator>(const FlatDigraph& b) const {
    return (this->cmp(b) > 0);
  }
  bool operator>=(const FlatDigraph& b) const {
    return (this->cmp(b) >= 0);
  }
};

uint domsz_of(const LocalLegit& legit) { return legit.vals.sz(); }

  void
config_enum_idx_fo(LocalConfig& config, uint idx, uint domsz)
{
  uint doms[3];
  uint tmp[3];
  doms[0] = doms[1] = doms[2] = domsz;
  state_of_index (tmp, idx, doms, 3);
  config.x_id = tmp[0];
  config.x_pd = tmp[1];
  config.x_sc = tmp[2];
}

Cx::OFile& operator<<(Cx::OFile& of, const LocalConfig& config)
{
  of << config.x_pd << "," << config.x_id << "," << config.x_sc;
  return of;
}

Cx::OFile& operator<<(Cx::OFile& of, const LocalCont& cont)
{
  of << cont.x_id << "," << cont.x_sc;
  return of;
}

Cx::OFile& operator<<(Cx::OFile& of, const BitTable& bt)
{
  for (ujint i = 0; i < bt.sz; ++i)
    of << (ck_BitTable (bt, i) ? '1' : '0');
  return of;
}

Cx::OFile& operator<<(Cx::OFile& of, const Cx::BitTable& bt)
{
  for (ujint i = 0; i < bt.sz(); ++i)
    of << bt[i];
  return of;
}

  void
rm_config(LocalLegit& legit, uint config_enum_idx)
{
  LocalConfig config;
  config_enum_idx_fo(config, config_enum_idx, domsz_of(legit));
}

  void
construct(LocalLegit& legit, const BitTable set)
{
  const uint domsz = domsz_of(legit);
  Claim2( domsz*domsz*domsz ,==, set.sz );

  for (ujint config_enum_idx = begidx_BitTable (set);
       config_enum_idx < set.sz;
       config_enum_idx = nextidx_BitTable (set, config_enum_idx))
  {
    uint config_idx = legit.configs.sz();
    LocalConfig& config = legit.configs.grow1();
    config_enum_idx_fo(config, config_enum_idx, domsz);

    legit.vals[config.x_id].configs.push(config_idx);
    Cx::Tuple<uint,2> key;

    key[0] = config.x_id;
    key[1] = config.x_sc;
    config.sc_cont_idx = legit.cont_map.ensure(key, legit.conts.sz());
    if (config.sc_cont_idx == legit.conts.sz()) {
      LocalCont& cont = legit.conts.grow1();
      cont.x_id = config.x_id;
      cont.x_sc = config.x_sc;
    }

    key[0] = config.x_pd;
    key[1] = config.x_id;
    uint cont_idx = legit.cont_map.ensure(key, legit.conts.sz());
    if (cont_idx == legit.conts.sz()) {
      LocalCont& cont = legit.conts.grow1();
      cont.x_id = config.x_pd;
      cont.x_sc = config.x_id;
    }
    legit.conts[cont_idx].sc_configs.push(config_idx);
  }
}

  void
oput_graph(Cx::OFile& of, const LocalLegit& legit)
{
  const uint val_offset = 0;
  const uint config_offset = legit.vals.sz();
  const uint cont_offset = config_offset + legit.configs.sz();

  for (uint i = 0; i < legit.vals.sz(); ++i) {
    of << (val_offset + i) << " -> " << (val_offset + i) << '\n';
    of << "# " << i << " -> " << (val_offset + i) << '\n';
    for (uint j = 0; j < legit.vals[i].configs.sz(); ++j) {
      of << (val_offset + i) << " -> " << (config_offset + legit.vals[i].configs[j]) << '\n';
      of << "# " << i << " -> " << legit.configs[legit.vals[i].configs[j]] << "\n";
    }
  }
  for (uint i = 0; i < legit.configs.sz(); ++i) {
    of << (config_offset + i) << " -> " << (cont_offset + legit.configs[i].sc_cont_idx) << '\n';
    of << "# " << legit.configs[i] << " -> " << legit.conts[legit.configs[i].sc_cont_idx] << '\n';
  }
  for (uint i = 0; i < legit.conts.sz(); ++i) {
    of << (cont_offset + i) << " -> " << (val_offset + legit.conts[i].x_sc) << '\n';
    of << "# " << legit.conts[i] << " -> " << legit.conts[i].x_sc << '\n';
    for (uint j = 0; j < legit.conts[i].sc_configs.sz(); ++j) {
      of << (cont_offset + i) << " -> " << (config_offset + legit.conts[i].sc_configs[j]) << '\n';
      of << "# " << legit.conts[i] << " -> " << legit.configs[legit.conts[i].sc_configs[j]] << '\n';
    }
  }
}

  void
construct_graph(Cx::Table< Cx::Table<uint> >& graph, const LocalLegit& legit)
{
  const uint val_offset = 0;
  const uint config_offset = val_offset + legit.vals.sz();
  const uint cont_offset = config_offset + legit.configs.sz();

  const uint nvertices = legit.vals.sz() + legit.configs.sz() + legit.conts.sz();
  graph.resize(nvertices);

  for (uint i = 0; i < legit.vals.sz(); ++i) {
    Cx::Table<uint>& edges = graph[val_offset+i];
    edges.resize(1+legit.vals[i].configs.sz());
    edges[0] = (val_offset + i);
    for (uint j = 0; j < legit.vals[i].configs.sz(); ++j) {
      edges[1+j] = (config_offset + legit.vals[i].configs[j]);
    }
  }
  for (uint i = 0; i < legit.configs.sz(); ++i) {
    Cx::Table<uint>& edges = graph[config_offset+i];
    edges.resize(1);
    edges[0] = (cont_offset + legit.configs[i].sc_cont_idx);
  }
  for (uint i = 0; i < legit.conts.sz(); ++i) {
    Cx::Table<uint>& edges = graph[cont_offset + i];
    edges.resize(1+legit.conts[i].sc_configs.sz());
    edges[0] = (val_offset + legit.conts[i].x_sc);
    for (uint j = 0; j < legit.conts[i].sc_configs.sz(); ++j) {
      edges[1+j] = (config_offset + legit.conts[i].sc_configs[j]);
    }
  }
}

  void
construct_graph(Cx::Table< Cx::Table<uint> >& graph, const BitTable& set, const uint domsz)
{
  LocalLegit legit( domsz );
  construct(legit, set);
  construct_graph(graph, legit);
}

  void
dimacs_graph(Cx::OFile& of, const BitTable& set, const uint domsz)
{
  Cx::Table< Cx::Table<uint> > graph;
  construct_graph(graph, set, domsz);

  uint nedges = 0;
  for (uint i = 0; i < graph.sz(); ++i) {
    nedges += graph[i].sz();
  }

  of << "p edge " << graph.sz() << ' ' << nedges << '\n';
  for (uint i = 0; i < graph.sz(); ++i) {
    for (uint j = 0; j < graph[i].sz(); ++j) {
      of << "e " << (1+i) << ' ' << (1+graph[i][j]) << '\n';
    }
  }
}

  void
permute_pc_config (Cx::BitTable& bt, const BitTable set, const Cx::Table<uint>& perm_map)
{
  uint doms[3];
  doms[0] = doms[1] = doms[2] = perm_map.sz();
  bt.wipe(0);
  for (ujint i = 0; i < set.sz; ++i) {
    uint vals[3];
    if (ck_BitTable (set, i)) {
      state_of_index (vals, i, doms, 3);
      for (uint j = 0; j < 3; ++j) {
        vals[j] = perm_map[vals[j]];
      }
      bt[index_of_state (vals, doms, 3)] = 1;
    }
  }
}

  bool
minimal_unique_ck (const uint* a, uint n)
{
  Cx::BitTable hits(n, 0);

  for (uint i = 0; i < n; ++i)
  {
    if (a[i] >= n)
      return false;
    if (hits[a[i]] != 0)
      return false;
    hits[a[i]] = 1;
  }
  return true;
}


static inline
  void
pc_config_of_enum_idx (uint* config, uint config_enum_idx, const uint domsz)
{
  uint tmp[3];
  uint doms[3];
  doms[0] = doms[1] = doms[2] = domsz;
  state_of_index (tmp, config_enum_idx, doms, 3);
  config[0] = tmp[1];
  config[1] = tmp[0];
  config[2] = tmp[2];
}

static inline
  uint
enum_idx_of_pc_config (const uint* config, const uint domsz)
{
  uint tmp[3];
  uint doms[3];
  doms[0] = doms[1] = doms[2] = domsz;
  tmp[0] = config[1];
  tmp[1] = config[0];
  tmp[2] = config[2];
  return index_of_state (tmp, doms, 3);
}

static inline
  uint
biring_continuations (uint* conts, uint config_enum_idx, const BitTable set, const uint domsz)
{
  uint n = 0;
  uint config[3];

  pc_config_of_enum_idx (config, config_enum_idx, domsz);

  config[0] = config[1];
  config[1] = config[2];
  for (uint i = 0; i < domsz; ++i) {
    config[2] = i;
    uint idx = enum_idx_of_pc_config (config, domsz);
    if (ck_BitTable (set, idx)) {
      conts[n++] = idx;
    }
  }
  return n;
}


  void
biring_fixpoint(BitTable img_set, uint domsz)
{
  Cx::Table<uint> conts(domsz);
  BitTable pre_set = cons1_BitTable (img_set.sz);

  do
  {
    op_BitTable (pre_set, BitOp_IDEN1, img_set);
    wipe_BitTable (img_set, 0);
    for (uint config_enum_idx = begidx_BitTable (pre_set);
         config_enum_idx < pre_set.sz;
         config_enum_idx = nextidx_BitTable (pre_set, config_enum_idx))
    {
      uint n = biring_continuations(&conts[0], config_enum_idx, pre_set, domsz);
      for (uint i = 0; i < n; ++i) {
        set1_BitTable (img_set, conts[i]);
      }
    }
  } while (0 != cmp_BitTable (pre_set, img_set));
  lose_BitTable (&pre_set);
}

  bool
biring_sat_ck (const BitTable set, const uint domsz)
{
  Cx::BitTable reach_pre( set.sz, 0 );
  Cx::BitTable reach_img( set.sz, 0 );
  const uint N = set.sz;
  const uint N_0 = 2;
  Cx::BitTable sats( N+1, 0 );
  Cx::Table<uint> conts(domsz);

  for (uint config_enum_idx = begidx_BitTable (set);
       config_enum_idx < set.sz;
       config_enum_idx = nextidx_BitTable (set, config_enum_idx))
  {
    reach_img.wipe(0);

    uint n = biring_continuations(&conts[0], config_enum_idx, set, domsz);
    for (uint i = 0; i < n; ++i) {
      reach_img[conts[i]] = 1;
    }

    for (uint step_idx = 1; step_idx < N; ++step_idx) {
      reach_pre = reach_img;
      reach_img.wipe(0);
      for (uint idx = reach_pre.begidx(); idx < reach_pre.sz(); idx = reach_pre.nextidx(idx))
      {
        uint n = biring_continuations(&conts[0], idx, set, domsz);
        for (uint i = 0; i < n; ++i) {
          reach_img[conts[i]] = 1;
        }
      }
      if (reach_img[config_enum_idx]) {
        sats[step_idx+1] = 1;
      }
    }
    for (uint i = N_0; i < N+1; ++i) {
      if (0 == sats[i])  break;
      if (i == N)  return true;
    }
  }
  return false;
}

#ifdef UseBlissLib
  void
flat_canonical_digraph(FlatDigraph& flat, Cx::BitTable& bt, const BitTable set, const uint domsz)
{
  Cx::Table< Cx::Table<uint> > graph;
  construct_graph(graph, set, domsz);

  const uint nvertices = graph.sz();
  bliss::Digraph bliss_graph(nvertices);
  bliss_graph.set_splitting_heuristic(bliss_graph.shs_fsm);
  bliss_graph.set_component_recursion(false);

  for (uint i = 0; i < graph.sz(); ++i) {
    for (uint j = 0; j < graph[i].sz(); ++j) {
      bliss_graph.add_edge(i, graph[i][j]);
    }
  }

  bliss::Stats stats;
  const unsigned int* perm =
    bliss_graph.canonical_form (stats, 0, 0);

  {
    Cx::Table<uint> perm_map(domsz);
    Cx::Table<uint> perm_ord(domsz);
    for (uint i = 0; i < domsz; ++i) {
      perm_ord[i] = perm[i];
    }
    std::sort(perm_ord.begin(), perm_ord.end());
    for (uint i = 0; i < domsz; ++i) {
      for (uint j = 0; j < domsz; ++j) {
        if (perm_ord[i] == perm[j]) {
          perm_map[j] = i;
        }
      }
    }
    //Claim( minimal_unique_ck (&perm_map[0], domsz) );
    bt = set;
    permute_pc_config (bt, set, perm_map);
  }

  Cx::Table< Cx::Table<uint> > graph2( graph );
  for (uint i = 0; i < graph.sz(); ++i) {
    graph2[perm[i]] = graph[i];
  }
  flat = graph2;
}
#endif

  void
canonical_set(Cx::BitTable& min_bt, const BitTable set, const uint domsz)
{
  Cx::Table<uint> perm_doms(domsz-1);
  ujint nperms = 1;
  for (uint i = 0; i < perm_doms.sz(); ++i) {
    perm_doms[i] = domsz - i;
    nperms *= perm_doms[i];
  }
  Cx::Table<uint> perm_vals(domsz-1);
  Cx::Table<uint> perm_map(domsz);
  min_bt = set;
  Cx::BitTable bt(set);

  for (ujint perm_idx = 0; perm_idx < nperms; ++perm_idx) {
    state_of_index (&perm_vals[0], perm_idx, perm_doms);
    for (uint i = 0; i < domsz; ++i) {
      perm_map[i] = i;
    }
    for (uint i = 0; i < perm_vals.sz(); ++i) {
      SwapT( uint, perm_map[i], perm_map[i+perm_vals[i]] );
    }
    //Claim( minimal_unique_ck(&perm_map[0], perm_map.sz()) );
    permute_pc_config (bt, set, perm_map);
    if (bt > min_bt) {
      min_bt = bt;
    }
  }
}

  void
flat_canonical_hack (FlatDigraph& flat, const Cx::BitTable min_bt)
{
  Cx::Table< Cx::Table<uint> > list1;
  Cx::Table<uint>& list = list1.grow1();
  for (ujint i = 0; i < min_bt.sz(); ++i) {
    if (min_bt[i]) {
      list.push(i);
    }
  }
  flat = list1;
}

  void
oput_biring_invariant (Cx::OFile& ofile, const Cx::BitTable& legit, const uint domsz,
                       const char* pfx = "", const char* delim = " || ")
{
  for (ujint config_enum_idx = legit.begidx();
       config_enum_idx < legit.sz();
       config_enum_idx = legit.nextidx(config_enum_idx))
  {
    ofile << pfx;
    pfx = delim;

    uint config[3];
    pc_config_of_enum_idx (config, config_enum_idx, domsz);
    ofile
      << "(x[i-1]==" << config[0]
      << " && x[i]==" << config[1]
      << " && x[i+1]==" << config[2] << ")";
  }
}

  void
oput_biring_protocon_spec (const Cx::String& ofilepath, const Cx::String& ofilename,
                           const Cx::BitTable& legit, const uint domsz)
{
  Cx::OFileB ofile;
  ofile.open(ofilepath, ofilename);
  ofile
    << "constant N := 3;\n"
    << "constant M := " << domsz << ";\n"
    << "variable x[Nat % N] <- Nat % M;\n"
    << "process P[i <- Nat % N]\n"
    << "{\n"
    << "read: x[i-1];\n"
    << "write: x[i];\n"
    << "read: x[i+1];\n"
    << "invariant: 0==1";
  oput_biring_invariant (ofile, legit, domsz, "\n|| ", "\n|| ");
  ofile
    << "\n;\n"
    << "}";
}

  void
#ifdef UseBitTableDB
recurse(const BitTable bt, const uint domsz, uint q, Cx::Set<Cx::BitTable>& db)
#else
recurse(const BitTable bt, const uint domsz, uint q, Cx::Set<FlatDigraph>& db)
#endif
{
  //if (q < bt.sz - 15)  return;

  BitTable set = cons1_BitTable (bt.sz);
  op_BitTable (set, BitOp_IDEN1, bt);
  biring_fixpoint (set, domsz);

  Cx::String ofilename;
  {
    Cx::C::OFile name_ofile;
    init_OFile (&name_ofile);
    {
      Cx::OFile tmp_ofile(&name_ofile);
      tmp_ofile << set;
    }
    ofilename = ccstr1_of_OFile (&name_ofile, 0);
    lose_OFile (&name_ofile);
  }
  Cx::OFile stat_ofile( stdout_OFile () );

  if (!biring_sat_ck (set, domsz)) {
    lose_BitTable (&set);
    //stat_ofile << ofilename << " unsat\n";
    return;
  }

#if 0
  {
    Cx::OFileB graph_ofile;
    graph_ofile.open("xbliss", ofilename);
    dimacs_graph (graph_ofile, set, domsz);
  }
#endif
  {
    FlatDigraph digraph;
    Cx::BitTable min_bt;
#if 0
    flat_canonical_digraph(digraph, min_bt, set, domsz);
    flat_canonical_hack(digraph, min_bt);
#else
    canonical_set(min_bt, set, domsz);
#ifndef UseBitTableDB
    flat_canonical_hack(digraph, min_bt);
#endif
#endif

#ifdef UseBitTableDB
    if (db.elem_ck(min_bt)) {
#else
    if (db.elem_ck(digraph)) {
#endif
      //stat_ofile << ofilename << ' ' << min_bt << " visited\n";
      lose_BitTable (&set);
      return;
    }
#ifdef UseBitTableDB
    db << min_bt;
#else
    db << digraph;
#endif
    //stat_ofile << ofilename << ' ' << min_bt << '\n';
    //stat_ofile << bt << ' ' << min_bt << '\n';
    stat_ofile << min_bt;
    oput_biring_invariant (stat_ofile, min_bt, domsz, "\n", " || ");
    stat_ofile << '\n';
    //oput_biring_protocon_spec ("../trial/ss3/spec", ofilename + ".protocon", min_bt, domsz);
  }
  if (q == 0) {
    lose_BitTable (&set);
    return;
  }

  while (q > 0)
  {
    q -= 1;
    if (!set0_BitTable (set, q))
      continue;

    recurse(set, domsz, q, db);
    set1_BitTable (set, q);
  }
  lose_BitTable (&set);
}

  void
searchit(const uint domsz)
{
  BitTable set = cons2_BitTable (domsz*domsz*domsz, 1);
  for (uint val = 0; val < domsz; ++val) {
    uint config[3];
    uint doms[3];
    config[0] = config[1] = config[2] = val;
    doms[0] = doms[1] = doms[2] = domsz;
    uint config_enum_idx = index_of_state (config, doms, 3);
    set0_BitTable (set, config_enum_idx);
  }

#ifdef UseBitTableDB
  Cx::Set<Cx::BitTable> db;
#else
  Cx::Set<FlatDigraph> db;
#endif
  recurse(set, domsz, set.sz, db);
  lose_BitTable (&set);
}

int main(int argc, char** argv)
{
  int argi = (init_sysCx (&argc, &argv), 1);
  if (argi < argc) {
    failout_sysCx ("No arguments expected!");
  }
  Cx::OFile of( stdout_OFile () );
  const uint domsz = 3;
  //BitTable set = cons2_BitTable (domsz*domsz*domsz, 0);
  //set1_BitTable (set, 1);
  //set1_BitTable (set, 2);
  //set1_BitTable (set, 3);
  //dimacs_graph(of, set, domsz);
  //lose_BitTable (&set);

  searchit(domsz);
  lose_sysCx ();
  return 0;
}

