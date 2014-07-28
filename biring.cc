
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

struct FilterOpt
{
  uint domsz;
  bool count_ones;
  bool subck_known;
  bool ppgck;
  bool xlate_invariant;
  const char* spec_ofilename;
  const char* graphviz_ofilename;

  FilterOpt()
    : domsz( 3 )
    , count_ones( false )
    , subck_known( false )
    , ppgck( false )
    , xlate_invariant( false )
    , spec_ofilename( 0 )
    , graphviz_ofilename( 0 )
  {}
};

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

static bool
biring_legit_enum_idx (const BitTable set, uint config_enum_idx, uint domsz,
                       BitTable cache, BitTable frontier)
{
  Cx::Table<uint> conts(domsz);
  wipe_BitTable (cache, 0);
  set1_BitTable (cache, config_enum_idx);
  wipe_BitTable (frontier, 0);
  set1_BitTable (frontier, config_enum_idx);
  bool found = false;
  for (uint idx = config_enum_idx; idx < set.sz; idx = begidx_BitTable (frontier)) {
    set0_BitTable (frontier, idx);
    uint n = biring_continuations (&conts[0], idx, set, domsz);
    for (uint i = 0; i < n; ++i) {
      if (conts[i] == config_enum_idx) {
        found = true;
        break;
      }
      if (!ck_BitTable (cache, conts[i])) {
        set1_BitTable (cache, conts[i]);
        set1_BitTable (frontier, conts[i]);
      }
    }
    if (found)  break;
  }
  return found;
}

#if 0
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

  bool done = false;
  while (!done)
  {
    done = true;
    for (uint config_enum_idx = begidx_BitTable (img_set);
         config_enum_idx < img_set.sz;
         config_enum_idx = nextidx_BitTable (img_set, config_enum_idx))
    {
      uint n = biring_continuations(&conts[0], config_enum_idx, img_set, domsz);
      if (n == 0) {
        set0_BitTable (img_set, config_enum_idx);
        done = false;
      }
    }
  }
}
#else
  void
biring_fixpoint(BitTable set, uint domsz)
{
  BitTable cache = cons1_BitTable (set.sz);
  BitTable frontier = cons1_BitTable (set.sz);
  for (uint config_enum_idx = begidx_BitTable (set);
       config_enum_idx < set.sz;
       config_enum_idx = nextidx_BitTable (set, config_enum_idx))
  {
    if (!biring_legit_enum_idx (set, config_enum_idx, domsz, cache, frontier)) {
      set0_BitTable (set, config_enum_idx);
    }
  }
  lose_BitTable (&cache);
  lose_BitTable (&frontier);
}
#endif

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

static
  bool
local_propagation_syn(const BitTable set, const uint domsz)
{
  BitTable cache = cons1_BitTable (set.sz);
  BitTable frontier = cons1_BitTable (set.sz);
  BitTable tmp_set = cons1_BitTable (set.sz);
  bool livesyn = true;
  for (uint config_enum_idx = 0; livesyn && config_enum_idx < set.sz; ++config_enum_idx) {
    uint config[3];
    if (ck_BitTable (set, config_enum_idx))
      continue;

    pc_config_of_enum_idx (config, config_enum_idx, domsz);

    livesyn = false;
    for (uint c = 0; c < domsz; ++c) {
      config[1] = c;
      uint idx = enum_idx_of_pc_config (config, domsz);
      if (ck_BitTable (set, idx)) {
        // Can fix P[i] by assigning x[i]:=c
        livesyn = true;
        break;
      }

      op_BitTable (tmp_set, BitOp_IDEN1, set);
      set1_BitTable (tmp_set, idx);
      if (!biring_legit_enum_idx (tmp_set, idx, domsz, cache, frontier)) {
        livesyn = true;
        break;
      }
    }
  }

  lose_BitTable (&cache);
  lose_BitTable (&frontier);
  lose_BitTable (&tmp_set);
  return livesyn;
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

static bool
subgraph_isomorphism_ck(const BitTable sub_a, const Cx::BitTable& b, uint domsz)
{
  Cx::BitTable a( sub_a );
  Cx::Table<uint> perm_doms(domsz-1);
  ujint nperms = 1;
  for (uint i = 0; i < perm_doms.sz(); ++i) {
    perm_doms[i] = domsz - i;
    nperms *= perm_doms[i];
  }
  Cx::Table<uint> perm_vals(domsz-1);
  Cx::Table<uint> perm_map(domsz);

  for (ujint perm_idx = 0; perm_idx < nperms; ++perm_idx) {
    state_of_index (&perm_vals[0], perm_idx, perm_doms);
    for (uint i = 0; i < domsz; ++i) {
      perm_map[i] = i;
    }
    for (uint i = 0; i < perm_vals.sz(); ++i) {
      SwapT( uint, perm_map[i], perm_map[i+perm_vals[i]] );
    }
    permute_pc_config (a, sub_a, perm_map);
    if (a.subseteq_ck(b)) {
      return true;
    }
  }
  return false;
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
    << "write: x[i];\n"
    << "read: x[i-1];\n"
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
    if (db.elem_ck(min_bt))
#else
    if (db.elem_ck(digraph))
#endif
    {
      //stat_ofile << ofilename << ' ' << min_bt << " visited\n";
      lose_BitTable (&set);
      return;
    }
#ifdef UseBitTableDB
    db << min_bt;
#else
    db << digraph;
#endif
    if (true || local_propagation_syn(set, domsz)) {
      //oput_biring_protocon_spec ("../trial/ss3/spec", ofilename + ".protocon", min_bt, domsz);
      //stat_ofile << ofilename << ' ' << min_bt << '\n';
      //stat_ofile << bt << ' ' << min_bt << '\n';
      stat_ofile << min_bt;
      // Print the invariant.
      //oput_biring_invariant (stat_ofile, min_bt, domsz, "\n", " || ");
      stat_ofile << '\n';
    }
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

static void
oput_graphviz(Cx::OFile& ofile, const BitTable set, uint domsz)
{
  ofile << "digraph G {\n"
    << " margin=0;\n"
    << " edge [weight=5];\n\n";

  for (uint config_enum_idx = begidx_BitTable (set);
       config_enum_idx < set.sz;
       config_enum_idx = nextidx_BitTable (set, config_enum_idx))
  {
    uint config[3];
    pc_config_of_enum_idx (config, config_enum_idx, domsz);
    ofile << "  config_" << config[0] << '_' << config[1]
      << " [label=\"" << config[1] << "\"];\n";
  }

  Cx::Table<uint> conts(domsz);
  for (uint config_enum_idx = begidx_BitTable (set);
       config_enum_idx < set.sz;
       config_enum_idx = nextidx_BitTable (set, config_enum_idx))
  {
    uint config_src[3];
    pc_config_of_enum_idx (config_src, config_enum_idx, domsz);
    uint n = biring_continuations(&conts[0], config_enum_idx, set, domsz);

    Cx::Set< Cx::Tuple<uint, 2> > cache;
    for (uint i = 0; i < n; ++i) {
      uint config_dst[3];
      pc_config_of_enum_idx (config_dst, conts[i], domsz);
      Cx::Tuple<uint,2> dst_tup(config_dst[0], config_dst[1]);
      if (cache.elem_ck(dst_tup))  continue;
      cache << dst_tup;
      ofile << "  "
        << "config_" << config_src[0] << '_' << config_src[1] << " -> "
        << "config_" << config_dst[0] << '_' << config_dst[1] << "\n";
    }
  }
  ofile << "}\n";
}

static bool
xget_BitTable (XFile* xfile, BitTable set)
{
  XFile olay[1];
  if (!getlined_olay_XFile (olay, xfile, "\n"))
    return false;
  skipds_XFile (olay, 0);
  wipe_BitTable (set, 0);
  for (uint i = 0; i < set.sz; ++i) {
    char c;
    if (!xget_char_XFile (olay, &c)) {
      if (i == 0) {
        return false;
      }
      else {
        failout_sysCx ("not enough characters!");
      }
    }
    if (c == '1') {
      set1_BitTable (set, i);
    }
  }
  return true;
}

static bool
subck_2match(const BitTable set, const uint domsz) {
  uint pc_configs[][3] = {
    { 0, 0, 1 },
    { 1, 0, 1 },
    { 0, 1, 0 },
    { 1, 0, 0 }
  };
  BitTable matching_set = cons2_BitTable (domsz*domsz*domsz, 0);
  for (uint i = 0; i < ArraySz(pc_configs); ++i) {
    uint enum_idx =
      enum_idx_of_pc_config (pc_configs[i], domsz);
    set1_BitTable (matching_set, enum_idx);
  }

  bool ret = subgraph_isomorphism_ck (matching_set, set, domsz);
  lose_BitTable (&matching_set);
  return ret;
}

static bool
subck_3match(const BitTable set, const uint domsz) {
  uint pc_configs[][3] = {
    { 0, 1, 0 },
    { 0, 1, 2 },
    { 1, 0, 1 },
    { 1, 2, 0 },
    { 2, 0, 1 }
  };
  BitTable matching_set = cons2_BitTable (domsz*domsz*domsz, 0);
  for (uint i = 0; i < ArraySz(pc_configs); ++i) {
    uint enum_idx =
      enum_idx_of_pc_config (pc_configs[i], domsz);
    set1_BitTable (matching_set, enum_idx);
  }

  bool ret = subgraph_isomorphism_ck (matching_set, set, domsz);
  lose_BitTable (&matching_set);
  return ret;
}

static bool
subck_next7(const BitTable set, const uint domsz) {
  uint pc_configs[][3] = {
    { 0, 0, 1 },
    { 0, 1, 0 },
    { 0, 1, 2 },
    { 1, 0, 0 },
    { 1, 2, 1 },
    { 2, 1, 0 },
    { 2, 1, 2 }
  };
  // 010100000101000101000010000
  BitTable matching_set = cons2_BitTable (domsz*domsz*domsz, 0);
  for (uint i = 0; i < ArraySz(pc_configs); ++i) {
    uint enum_idx =
      enum_idx_of_pc_config (pc_configs[i], domsz);
    set1_BitTable (matching_set, enum_idx);
  }

  bool ret = subgraph_isomorphism_ck (matching_set, set, domsz);
  lose_BitTable (&matching_set);
  return ret;
}

static bool
subck_next10(const BitTable set, const uint domsz) {
  Cx::Table<const char*> legit_strings;
  legit_strings
    << "010100110101000001000011100"
    << "010101101100000100101000010"
    << "010101111100000001100010000"
    << "011100011101000000100001100"
    << "011101000100000101001010010"
    << "011101011100000001100010000"
    << "010101101101000100100110000"
    << "010101111101000100100010000"
    << "011101011101000100100010000"
    << "011100011101000100110010000"
    << "010111110011100011100010000"
    << "011111010010101101100010000"
    << "010111101011100011101001010"
    << "011110011010101101100001110"
    ;
  BitTable matching_set = cons2_BitTable (domsz*domsz*domsz, 0);
  bool ret = false;
  for (uint known_idx = 0; known_idx < legit_strings.sz(); ++known_idx) {
    wipe_BitTable (matching_set, 0);
    for (uint i = 0; i < matching_set.sz; ++i) {
      if (legit_strings[known_idx][i] == '1') {
        set1_BitTable (matching_set, i);
      }
    }
    ret = subgraph_isomorphism_ck (matching_set, set, domsz);
    if (ret)  break;
  }
  lose_BitTable (&matching_set);
  return ret;
}


static void
filter_stdin (const FilterOpt& opt)
{
  const uint domsz = opt.domsz;
  BitTable set = cons1_BitTable (domsz*domsz*domsz);
  Cx::OFile ofile( stdout_OFile () );
  XFile* xfile = stdin_XFile ();
  while (xget_BitTable (xfile, set)) {
    ofile << set;
    if (opt.count_ones) {
      ofile << ' ' << count_BitTable (set);
    }
    if (opt.subck_known) {
      ofile << " 2match:" << (subck_2match (set, domsz) ? 'Y' : 'N');
      ofile << " 3match:" << (subck_3match (set, domsz) ? 'Y' : 'N');
      ofile << " next7:" << (subck_next7 (set, domsz) ? 'Y' : 'N');
      ofile << " next10:" << (subck_next10 (set, domsz) ? 'Y' : 'N');
    }
    if (opt.ppgck) {
      ofile << " ppg:" << (local_propagation_syn (set, domsz) ? 'Y' : 'N');
    }
    ofile << '\n';
    if (opt.xlate_invariant) {
      oput_biring_invariant (ofile, set, domsz, "", " || ");
      ofile << '\n';
    }
    if (opt.spec_ofilename) {
      oput_biring_protocon_spec ("", opt.spec_ofilename, set, domsz);
    }
    if (opt.graphviz_ofilename) {
      Cx::OFileB graphviz_ofile;
      graphviz_ofile.open(0, opt.graphviz_ofilename);
      oput_graphviz (graphviz_ofile, set, domsz);
    }
  }

  lose_BitTable (&set);
}

int main(int argc, char** argv)
{
  int argi = (init_sysCx (&argc, &argv), 1);
  bool filter = false;
  FilterOpt opt;

  while (argi < argc) {
    const char* arg = argv[argi++];
    if (eq_cstr ("-domsz", arg)) {
      if (!xget_uint_cstr (&opt.domsz, argv[argi++]))
        failout_sysCx("Argument Usage: -domsz n\nWhere n is an unsigned integer!");
    }
    else if (eq_cstr ("-xlate-invariant", arg)) {
      filter = true;
      opt.xlate_invariant = true;
    }
    else if (eq_cstr ("-count-ones", arg)) {
      filter = true;
      opt.count_ones = true;
    }
    else if (eq_cstr ("-subck-known", arg)) {
      filter = true;
      opt.subck_known = true;
    }
    else if (eq_cstr ("-ppgck", arg)) {
      filter = true;
      opt.ppgck = true;
    }
    else if (eq_cstr ("-o-graphviz", arg)) {
      filter = true;
      opt.graphviz_ofilename = argv[argi++];
      if (!opt.graphviz_ofilename)
        failout_sysCx("Argument Usage: -o-graphviz file");
    }
    else if (eq_cstr ("-o-spec", arg)) {
      filter = true;
      opt.spec_ofilename = argv[argi++];
      if (!opt.spec_ofilename)
        failout_sysCx("Argument Usage: -o-spec file");
    }
    else  {
      DBog1( "Unrecognized option: %s", arg );
      failout_sysCx (0);
    }
  }
  //Cx::OFile ofile( stdout_OFile () );
  //BitTable set = cons2_BitTable (domsz*domsz*domsz, 0);
  //set1_BitTable (set, 1);
  //set1_BitTable (set, 2);
  //set1_BitTable (set, 3);
  //dimacs_graph(ofile, set, domsz);
  //lose_BitTable (&set);

  if (filter) {
    filter_stdin (opt);
  }
  else {
    searchit(opt.domsz);
  }
  lose_sysCx ();
  return 0;
}

