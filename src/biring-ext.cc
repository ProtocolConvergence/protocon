
//#define UseBlissLib

#ifdef UseBlissLib
#include <graph.hh>
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

std::ostream& operator<<(std::ostream& of, const LocalConfig& config)
{
  of << config.x_pd << "," << config.x_id << "," << config.x_sc;
  return of;
}

std::ostream& operator<<(std::ostream& of, const LocalCont& cont)
{
  of << cont.x_id << "," << cont.x_sc;
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

  for (zuint config_enum_idx = begidx_BitTable (set);
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
oput_graph(std::ostream& of, const LocalLegit& legit)
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
dimacs_graph(std::ostream& of, const BitTable& set, const uint domsz)
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
flat_canonical_hack (FlatDigraph& flat, const Cx::BitTable min_bt)
{
  Cx::Table< Cx::Table<uint> > list1;
  Cx::Table<uint>& list = list1.grow1();
  for (zuint i = 0; i < min_bt.sz(); ++i) {
    if (min_bt[i]) {
      list.push(i);
    }
  }
  flat = list1;
}

