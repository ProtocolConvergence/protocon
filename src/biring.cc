
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

//#include "biring-ext.cc"
#define UseBitTableDB

struct FilterOpt
{
  uint domsz;
  uint minsz;
  bool pair;
  bool trivial;
  bool echo_bits;
  bool echo_subsets;
  bool count_ones;
  bool subck_known;
  bool subck_match;
  bool ppgck;
  bool xlate_invariant;
  bool grow_domsz;
  const char* spec_ofilename;
  const char* graphviz_ofilename;

  FilterOpt()
    : domsz( 3 )
    , minsz( 3 )
    , pair( false )
    , trivial( false )
    , echo_bits( false )
    , echo_subsets( false )
    , count_ones( false )
    , subck_known( false )
    , subck_match( false )
    , ppgck( false )
    , xlate_invariant( false )
    , grow_domsz( false )
    , spec_ofilename( 0 )
    , graphviz_ofilename( 0 )
  {}
};

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
  bool
ck_pc_config (const BitTable set, const uint domsz,
              const uint x_pd, const uint x_id, const uint x_sc)
{
  uint config[3];
  config[0] = x_pd;
  config[1] = x_id;
  config[2] = x_sc;
  return ck_BitTable (set, enum_idx_of_pc_config (config, domsz));
}

static inline
  void
biring_initials (Cx::Table<uint>& initials, uint config_enum_idx, const BitTable set, const uint domsz)
{
  initials.flush();
  uint config[3];
  pc_config_of_enum_idx (config, config_enum_idx, domsz);
  for (uint i = 0; i < domsz; ++i) {
    config[2] = i;
    uint idx = enum_idx_of_pc_config (config, domsz);
    if (ck_BitTable (set, idx)) {
      initials << idx;
    }
  }
}

static inline
  uint
direct_biring_continuations (uint* conts, uint config_enum_idx, const BitTable set, const uint domsz)
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

static inline
  void
biring_continuations (Cx::Table<uint>& conts, uint config_enum_idx, const BitTable set, const uint domsz)
{
  conts.flush();
  conts.grow(domsz);
  uint n = direct_biring_continuations (&conts[0], config_enum_idx, set, domsz);
  conts.cpop(domsz-n);
}

static bool
biring_legit_enum_idx (const BitTable set, uint config_enum_idx, uint domsz,
                       BitTable cache, BitTable frontier)
{
  Cx::Table<uint> conts;
  wipe_BitTable (cache, 0);
  set1_BitTable (cache, config_enum_idx);
  wipe_BitTable (frontier, 0);
  set1_BitTable (frontier, config_enum_idx);
  bool found = false;
  for (uint idx = config_enum_idx; idx < set.sz; idx = begidx_BitTable (frontier)) {
    set0_BitTable (frontier, idx);
    biring_continuations (conts, idx, set, domsz);
    for (uint i = 0; i < conts.sz(); ++i) {
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

/** Not actually better.**/
  bool
better_biring_sat_ck (const BitTable set, const uint domsz, const uint N_0)
{
  Cx::BitTable reach_pre( set.sz, 0 );
  Cx::BitTable reach_img( set.sz, 0 );
  Cx::Table<uint> conts;

  for (ujint config_enum_idx = begidx_BitTable (set);
       config_enum_idx < set.sz;
       config_enum_idx = nextidx_BitTable (set, config_enum_idx))
  {
    uint min_cycle = 0;
    uint nconsec = 0;
    reach_img.wipe(0);

    biring_initials(conts, config_enum_idx, set, domsz);
    for (uint i = 0; i < conts.sz(); ++i) {
      reach_img[conts[i]] = 1;
    }

    for (uint step_idx = 0; step_idx < N_0 + nconsec; ++step_idx)
    {
      /* DBog_ujint( step_idx ); */
      reach_pre = reach_img;
      reach_img.wipe(0);
      for (ujint idx = reach_pre.begidx(); idx < reach_pre.sz(); idx = reach_pre.nextidx(idx))
      {
        /* DBog_ujint( idx ); */
        biring_continuations(conts, idx, set, domsz);
        for (uint i = 0; i < conts.sz(); ++i) {
          /* DBog_ujint( conts[i] ); */
          reach_img[conts[i]] = 1;
        }
      }

      if (reach_img[config_enum_idx]) {
        if (min_cycle == 0)
          min_cycle = step_idx+1;

        nconsec += 1;
        if (nconsec == min_cycle)
          break;
      }
      else {
        nconsec = 0;
      }
    }

    if (nconsec != 0) {
      Claim2( nconsec ,==, min_cycle );
      return true;
    }
  }
  return false;
}

static void
img(Cx::BitTable& img_pf, const BitTable xn, const Cx::BitTable& pre_pf, uint domsz)
{
  img_pf.wipe(0);
  for (ujint enum_idx = pre_pf.begidx();
       enum_idx < pre_pf.sz();
       enum_idx = pre_pf.nextidx(enum_idx))
  {
    uint config[3];
    pc_config_of_enum_idx (config, enum_idx, domsz);

    config[0] = config[1];
    config[1] = config[2];

    for (uint i = 0; i < domsz; ++i) {
      config[2] = i;
      uint idx = enum_idx_of_pc_config (config, domsz);
      if (ck_BitTable (xn, idx)) {
        img_pf.set1(idx);
      }
    }
  }
}

/** For this routine, for every node, we perform a fixpoint iteration starting
 * from that node until either the set doesn't change or it has been visited
 * before.
 **/
  bool
true_biring_sat_ck (const BitTable xn, const uint domsz, uint* nsteps)
{
  Cx::BitTable pre_pf( xn.sz, 0 );
  Cx::BitTable img_pf( xn.sz, 0 );

  Cx::Set<Cx::BitTable> visited;
  for (ujint enum_idx = begidx_BitTable (xn);
       enum_idx < xn.sz;
       enum_idx = nextidx_BitTable (xn, enum_idx))
  {
    visited.clear();

    pre_pf.wipe(0);
    pre_pf.set1(enum_idx);

    while (!visited.elem_ck(pre_pf))
    {
      visited << pre_pf;
      img(img_pf, xn, pre_pf, domsz);
      if (img_pf.ck(enum_idx) && pre_pf==img_pf) {
        if (nsteps) {
          *nsteps = visited.sz();
        }
        return true;
      }
      pre_pf = img_pf;
    }
  }
  return false;
}

  bool
biring_sat_ck (const BitTable set, const uint domsz, const uint N_0)
{
#if 0
  return better_biring_sat_ck (set, domsz, N_0);
#endif
  uint N = 0;

  if (!true_biring_sat_ck (set, domsz, &N)) {
    return false;
  }
  N -= 1;
  if (N_0 == 0 || N < N_0) {
    return true;
  }

  Cx::BitTable pre_pf( set.sz, 0 );
  Cx::BitTable img_pf( set.sz, 0 );
  Cx::BitTable sats( N+1, 0 );

  for (ujint config_enum_idx = begidx_BitTable (set);
       config_enum_idx < set.sz;
       config_enum_idx = nextidx_BitTable (set, config_enum_idx))
  {
    pre_pf.wipe(0);
    pre_pf.set1(config_enum_idx);

    for (uint step_idx = 1; step_idx < N+1; ++step_idx) {
      img(img_pf, set, pre_pf, domsz);

      if (img_pf.ck(config_enum_idx)) {
        sats.set1(step_idx);
      }
      pre_pf = img_pf;
    }

    while (N >= N_0 && sats.ck(N)) {
      N -= 1;
    }
    if (N < N_0) {
      return true;
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
oput_biring_invariant (Cx::OFile& ofile, const Cx::BitTable& legit, const uint domsz,
                       const char* pfx = "", const char* delim = " || ",
                       const bool pair = false,
                       const bool print_own = true)
{
  if (!delim)
    delim = pfx;

  Cx::Set< Cx::Tuple<uint, 2> > cache;
  for (ujint config_enum_idx = legit.begidx();
       config_enum_idx < legit.sz();
       config_enum_idx = legit.nextidx(config_enum_idx))
  {
    uint config[3];
    pc_config_of_enum_idx (config, config_enum_idx, domsz);
    if (pair) {
      Cx::Tuple<uint,2> tup(config[0], config[1]);
      if (cache.elem_ck(tup))  continue;
      cache << tup;
    }

    ofile << pfx;
    pfx = delim;

    ofile << "(x[i-1]==" << config[0];
    if (print_own) {
      ofile << " && x[i]==" << config[1];
    }
    if (!pair) {
      ofile << " && x[i+1]==" << config[2];
    }
   ofile << ")";
  }
}

  void
oput_biring_protocon_spec (const Cx::String& ofilepath, const Cx::String& ofilename,
                           const Cx::BitTable& legit, const FilterOpt& opt)
{
  const uint domsz = opt.domsz;
  Cx::OFileB ofb;
  Cx::OFile ofile( ofb.uopen(ofilepath, ofilename) );

  ofile
    << "// " << legit
    << "\nconstant N := 3;"
    << "\nconstant M := " << (domsz + OneIf(opt.grow_domsz)) << ";"
    << "\nvariable x[Nat % N] <- Nat % M;"
    << "\nprocess P[i <- Nat % N]"
    << "\n{"
    << "\n  write: x[i];"
    << "\n  read: x[i-1];"
    << "\n  read: x[i+1];"
    << "\n  (future & silent)"
    << "\n    (0!=0"
    ;
  oput_biring_invariant (ofile, legit, domsz, "\n     || ", 0, opt.pair, true);
  ofile << "\n    );";
  if (opt.grow_domsz) {
    ofile
      << "\n  puppet:"
      << "\n    (   x[i-1]!=" << domsz
      << "\n     && x[i]!=" << domsz
      << "\n     && x[i+1]!=" << domsz
      ;
    oput_biring_invariant (ofile, legit, domsz, "\n     && !", 0, false, false);
    ofile
      << "\n     -->"
      << "\n     x[i]:=" << domsz << ";"
      << "\n    );"
      ;
  }
  ofile << "\n}\n";
}

  void
recurse(BitTable set, uint q,
#ifdef UseBitTableDB
        Cx::Set<Cx::BitTable>& db,
#else
        Cx::Set<FlatDigraph>& db,
#endif
        const FilterOpt& opt, Cx::OFile& ofile)
{
  biring_fixpoint (set, opt.domsz);

  Cx::String ofilename;
  {
    Cx::C::OFile name_ofile;
    init_OFile (&name_ofile);

    Cx::OFile tmp_ofile(&name_ofile);
    tmp_ofile << set;

    ofilename = ccstr1_of_OFile (&name_ofile, 0);
    lose_OFile (&name_ofile);
  }

  if (!biring_sat_ck (set, opt.domsz, opt.minsz)) {
    return;
  }

#if 0
  {
    Cx::OFileB graph_ofile;
    graph_ofile.open("xbliss", ofilename);
    dimacs_graph (graph_ofile, set, opt.domsz);
  }
#endif

  {
    Cx::BitTable min_bt;
#if 0
    FlatDigraph digraph;
    flat_canonical_digraph(digraph, min_bt, set, opt.domsz);
#else
    canonical_set(min_bt, set, opt.domsz);
#endif

#ifdef UseBitTableDB
    Cx::BitTable& db_elem = min_bt;
#else
    FlatDigraph& db_elem = digraph;
    flat_canonical_hack(digraph, min_bt);
#endif

    if (db.elem_ck(db_elem))
    {
      return;
    }
    db << db_elem;

    if (true || local_propagation_syn(set, opt.domsz)) {
      ofile << min_bt << '\n';
    }
  }
  if (q == 0) {
    return;
  }

  BitTable bt = cons1_BitTable (set.sz);

  while (q > 0)
  {
    q -= 1;
    if (!ck_BitTable (set, q))
      continue;

    op_BitTable (bt, BitOp_IDEN1, set);
    set0_BitTable (bt, q);

    if (opt.pair) {
      uint config[3];
      pc_config_of_enum_idx (config, q, opt.domsz);
      for (uint i = 0; i < opt.domsz; ++i) {
        config[2] = i;
        set0_BitTable (bt, enum_idx_of_pc_config (config, opt.domsz));
      }
    }

    recurse(bt, q, db, opt, ofile);
  }
  lose_BitTable (&bt);
}

  void
searchit(const FilterOpt& opt, Cx::OFile& ofile)
{
  const uint domsz = opt.domsz;
  BitTable set = cons2_BitTable (domsz*domsz*domsz, 1);
  if (!opt.trivial) {
    for (uint val = 0; val < domsz; ++val) {
      uint config[3];
      config[0] = config[1] = config[2] = val;
      if (!opt.pair) {
        set0_BitTable (set, enum_idx_of_pc_config (config, domsz));
      }
      else {
        for (uint i = 0; i < domsz; ++i) {
          config[2] = i;
          set0_BitTable (set, enum_idx_of_pc_config (config, domsz));
        }
      }
    }
  }

#ifdef UseBitTableDB
  Cx::Set<Cx::BitTable> db;
#else
  Cx::Set<FlatDigraph> db;
#endif
  recurse(set, set.sz, db, opt, ofile);
  lose_BitTable (&set);
}

static void
oput_graphviz(Cx::OFile& ofile, const BitTable set, uint domsz, bool pair)
{
#define NiceLooking
  ofile << "digraph G {\n"
    << " margin=0;\n"
    << " edge [weight=5];\n\n";

  if (pair) {

    for (uint i = 0; i < domsz; ++i) {
      ofile << "  config_" << i << " [label=\"" << i << "\"];\n";
    }

    Cx::Set< Cx::Tuple<uint, 2> > cache;
    for (uint config_enum_idx = begidx_BitTable (set);
         config_enum_idx < set.sz;
         config_enum_idx = nextidx_BitTable (set, config_enum_idx))
    {
      uint config[3];
      pc_config_of_enum_idx (config, config_enum_idx, domsz);

      Cx::Tuple<uint,2> tup(config[0], config[1]);

      if (cache.elem_ck(tup))  continue;
      cache << tup;

      ofile << "  "
        << "config_" << config[0] << " -> "
        << "config_" << config[1] << "\n";
    }
    ofile << "}\n";
    return;
  }

  for (ujint config_enum_idx = begidx_BitTable (set);
       config_enum_idx < set.sz;
       config_enum_idx = nextidx_BitTable (set, config_enum_idx))
  {
    uint config[3];
    pc_config_of_enum_idx (config, config_enum_idx, domsz);
#ifdef NiceLooking
    ofile << "  config_" << config[0] << '_' << config[1]
      << " [label=\"" << config[1] << "\"];\n";
#else
    ofile << "  config_" << config_enum_idx
      /* << " [label=\"" << config[1] << ':' << config_enum_idx << "\"];\n"; */
      /* << " [label=\"" << config[1] << "\"];\n"; */
      << " [label=\"" << config[0] << config[1] << config[2] << "\"];\n";
#endif
  }

  Cx::Table<uint> conts;
  for (uint config_enum_idx = begidx_BitTable (set);
       config_enum_idx < set.sz;
       config_enum_idx = nextidx_BitTable (set, config_enum_idx))
  {
    uint config_src[3];
    pc_config_of_enum_idx (config_src, config_enum_idx, domsz);
    biring_continuations(conts, config_enum_idx, set, domsz);

    Cx::Set< Cx::Tuple<uint, 2> > cache;
    for (uint i = 0; i < conts.sz(); ++i) {
#ifdef NiceLooking
      uint config_dst[3];
      pc_config_of_enum_idx (config_dst, conts[i], domsz);
      Cx::Tuple<uint,2> dst_tup(config_dst[0], config_dst[1]);
      if (cache.elem_ck(dst_tup))  continue;
      cache << dst_tup;
      ofile << "  "
        << "config_" << config_src[0] << '_' << config_src[1] << " -> "
        << "config_" << config_dst[0] << '_' << config_dst[1] << "\n";
#else
      ofile << "  "
        << "config_" << config_enum_idx << " -> "
        << "config_" << conts[i] << "\n";
#endif
    }
  }
  ofile << "}\n";
#ifdef NiceLooking
#undef NiceLooking
#endif
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


/** Test whether there exists some a,b,c,d such that
 *   (a!=b && a!=c && a!=d) || (a==b && a==c && a==d)
 * and the following are all legitimate states for (x[i-1],x[i],x[i+1]):
 *   (a,b,a)
 *   (a,c,d)
 *   (b,a,b)
 *   (b,a,c)
 *   (c,d,a)
 *   (d,a,b)
 *   (d,a,c)
 **/
static bool
subck_match(const BitTable set, const uint domsz)
{
  for (uint a = 0; a < domsz; ++a) {
    for (uint b = 0; b < domsz; ++b) {

      if (!ck_pc_config (set, domsz, a, b, a))  continue;
      if (!ck_pc_config (set, domsz, b, a, b))  continue;

      if (a == b)  return true;

      for (uint c = 0; c < domsz; ++c) {
        if (c == a)  continue;
        if (!ck_pc_config (set, domsz, b, a, c))  continue;
        for (uint d = 0; d < domsz; ++d) {
          if (d == a)  continue;
          if (!ck_pc_config (set, domsz, a, c, d))  continue;
          if (!ck_pc_config (set, domsz, c, d, a))  continue;
          if (!ck_pc_config (set, domsz, d, a, b))  continue;
          if (!ck_pc_config (set, domsz, d, a, c))  continue;
          return true;
        }
      }
    }
  }
  return false;
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
echo_subsets (const BitTable bt, const FilterOpt& opt, Cx::OFile& ofile)
{
  Cx::Set<Cx::BitTable> db;
  BitTable set = cons1_BitTable (bt.sz);

  for (ujint idx = begidx_BitTable (bt);
       idx < bt.sz;
       idx = nextidx_BitTable (bt, idx))
  {
    op_BitTable (set, BitOp_IDEN1, bt);
    set0_BitTable (set, idx);
    biring_fixpoint (set, opt.domsz);
    if (biring_sat_ck (set, opt.domsz, opt.minsz)) {
      Cx::BitTable min_bt;
      canonical_set(min_bt, set, opt.domsz);
      if (!db.elem_ck(min_bt)) {
        db << min_bt;
        ofile << ' ' << min_bt;
      }
    }
  }
  lose_BitTable (&set);
}

static void
filter_stdin (const FilterOpt& opt, Cx::OFile& ofile)
{
  const uint domsz = opt.domsz;
  BitTable set = cons1_BitTable (domsz*domsz*domsz);
  XFile* xfile = stdin_XFile ();
  while (xget_BitTable (xfile, set)) {
    if (opt.echo_bits) {
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
      if (opt.subck_match) {
        ofile << " match:" << (subck_match (set, domsz) ? 'Y' : 'N');
      }
      if (opt.ppgck) {
        ofile << " ppg:" << (local_propagation_syn (set, domsz) ? 'Y' : 'N');
      }

      if (opt.echo_subsets) {
        echo_subsets(set, opt, ofile);
      }
      ofile << '\n';
    }

    if (opt.xlate_invariant) {
      oput_biring_invariant (ofile, set, domsz, "", " || ", opt.pair);
      ofile << '\n';
    }
    if (opt.spec_ofilename) {
      oput_biring_protocon_spec ("", opt.spec_ofilename, set, opt);
    }
    if (opt.graphviz_ofilename) {
      Cx::OFileB graphviz_ofileb;
      Cx::OFile graphviz_ofile( graphviz_ofileb.uopen(0, opt.graphviz_ofilename) );
      oput_graphviz (graphviz_ofile, set, domsz, opt.pair);
    }
  }

  lose_BitTable (&set);
}

int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);
  bool filter = false;
  FilterOpt opt;

  while (argi < argc) {
    const char* arg = argv[argi++];
    if (eq_cstr ("-domsz", arg)) {
      if (!xget_uint_cstr (&opt.domsz, argv[argi++]))
        failout_sysCx("Argument Usage: -domsz n\nWhere n is an unsigned integer!");
    }
    else if (eq_cstr ("-minsz", arg)) {
      if (!xget_uint_cstr (&opt.minsz, argv[argi++]))
        failout_sysCx("Argument Usage: -minsz n\nWhere n is an unsigned integer!");
    }
    else if (eq_cstr ("-pair", arg)) {
      opt.pair = true;
    }
    else if (eq_cstr ("-all", arg)) {
      opt.trivial = true;
    }
    else if (eq_cstr ("-xlate-invariant", arg)) {
      filter = true;
      opt.xlate_invariant = true;
    }
    else if (eq_cstr ("-echo", arg)) {
      filter = true;
      opt.echo_bits = true;
    }
    else if (eq_cstr ("-count-ones", arg)) {
      filter = true;
      opt.count_ones = true;
    }
    else if (eq_cstr ("-subck-known", arg)) {
      filter = true;
      opt.subck_known = true;
    }
    else if (eq_cstr ("-subck-match", arg)) {
      filter = true;
      opt.subck_match = true;
    }
    else if (eq_cstr ("-ppgck", arg)) {
      filter = true;
      opt.ppgck = true;
    }
    else if (eq_cstr ("-echo-subsets", arg)) {
      filter = true;
      opt.echo_bits = true;
      opt.echo_subsets = true;
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
    else if (eq_cstr ("-grow-domsz", arg)) {
      opt.grow_domsz = true;
    }
    else  {
      DBog1( "Unrecognized option: %s", arg );
      failout_sysCx (0);
    }
  }
  Cx::OFile ofile( stdout_OFile () );
  //BitTable set = cons2_BitTable (domsz*domsz*domsz, 0);
  //set1_BitTable (set, 1);
  //set1_BitTable (set, 2);
  //set1_BitTable (set, 3);
  //dimacs_graph(ofile, set, domsz);
  //lose_BitTable (&set);

  if (filter) {
    filter_stdin (opt, ofile);
  }
  else {
    searchit(opt, ofile);
  }
  lose_sysCx ();
  return 0;
}

