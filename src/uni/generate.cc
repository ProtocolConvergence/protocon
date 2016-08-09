
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
#include "uniact.hh"

using Cx::mk_Tuple;

struct FilterOpt
{
  uint domsz;
  uint minsz;
  bool trivial;
  bool echo_bits;
  bool echo_subsets;
  bool count_ones;
  bool ppgck;
  bool xlate_invariant;
  const char* spec_ofilename;
  const char* graphviz_ofilename;

  FilterOpt()
    : domsz( 3 )
    , minsz( 3 )
    , trivial( false )
    , echo_bits( false )
    , echo_subsets( false )
    , count_ones( false )
    , ppgck( false )
    , xlate_invariant( false )
    , spec_ofilename( 0 )
    , graphviz_ofilename( 0 )
  {}
};

Cx::OFile& operator<<(Cx::OFile& of, const BitTable& bt)
{
  for (zuint i = 0; i < bt.sz; ++i)
    of << (ck_BitTable (bt, i) ? '1' : '0');
  return of;
}

Cx::OFile& operator<<(Cx::OFile& of, const Cx::BitTable& bt)
{
  for (zuint i = 0; i < bt.sz(); ++i)
    of << bt[i];
  return of;
}

  void
permute_pc_act (Cx::BitTable& bt, const BitTable set, const Cx::Table<uint>& perm_map)
{
  const UniAct doms( perm_map.sz() );
  bt.wipe(0);
  for (zuint i = 0; i < set.sz; ++i) {
    UniAct vals;
    if (ck_BitTable (set, i)) {
      state_of_index(&vals[0], i, &doms[0], 3);
      for (uint j = 0; j < 3; ++j) {
        vals[j] = perm_map[vals[j]];
      }
      bt[index_of_state(&vals[0], &doms[0], 3)] = 1;
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
  UniAct
pc_act_of_enum_idx(uint act_enum_idx, const uint domsz)
{
  UniAct doms( domsz );
  UniAct tmp;
  state_of_index(&tmp[0], act_enum_idx, &doms[0], 3);
  return UniAct( tmp[1], tmp[0], tmp[2] );
}

static inline
  uint
enum_idx_of_pc_act(const UniAct& act, const uint domsz)
{
  UniAct tmp(act[1], act[0], act[2]);
  UniAct doms;
  doms.wipe(domsz);
  return index_of_state(&tmp[0], &doms[0], 3);
}

// TODO: Remove.
#define enum_idx_of_pc_config enum_idx_of_pc_act

static inline
  bool
ck_pc_act(const BitTable set, const uint domsz,
          const uint x_pd, const uint x_id, const uint x_sc)
{
  const UniAct act(x_pd, x_id, x_sc);
  return ck_BitTable(set, enum_idx_of_pc_act(act, domsz));
}

static inline
  uint
direct_biring_continuations (uint* conts, uint config_enum_idx, const BitTable set, const uint domsz)
{
  uint n = 0;
  UniAct config = pc_act_of_enum_idx(config_enum_idx, domsz);

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

/** Trim out all actions that are not involved in any periodic propagations.
 * These are trivial to detect.
 **/
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

static void
img(Cx::BitTable& img_pf, const BitTable xn, const Cx::BitTable& pre_pf, uint domsz)
{
  img_pf.wipe(0);
  for (zuint enum_idx = pre_pf.begidx();
       enum_idx < pre_pf.sz();
       enum_idx = pre_pf.nextidx(enum_idx))
  {
    UniAct config = pc_act_of_enum_idx(enum_idx, domsz);

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
  for (zuint enum_idx = begidx_BitTable (xn);
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

  for (zuint config_enum_idx = begidx_BitTable (set);
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
    if (ck_BitTable (set, config_enum_idx))
      continue;

    UniAct config = pc_act_of_enum_idx(config_enum_idx, domsz);

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
  luint nperms = 1;
  for (uint i = 0; i < perm_doms.sz(); ++i) {
    perm_doms[i] = domsz - i;
    nperms *= perm_doms[i];
  }
  Cx::Table<uint> perm_vals(domsz-1);
  Cx::Table<uint> perm_map(domsz);
  min_bt = set;
  Cx::BitTable bt(set);

  for (luint perm_idx = 0; perm_idx < nperms; ++perm_idx) {
    state_of_index (&perm_vals[0], perm_idx, perm_doms);
    for (uint i = 0; i < domsz; ++i) {
      perm_map[i] = i;
    }
    for (uint i = 0; i < perm_vals.sz(); ++i) {
      SwapT( uint, perm_map[i], perm_map[i+perm_vals[i]] );
    }
    //Claim( minimal_unique_ck(&perm_map[0], perm_map.sz()) );
    permute_pc_act (bt, set, perm_map);
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
  luint nperms = 1;
  for (uint i = 0; i < perm_doms.sz(); ++i) {
    perm_doms[i] = domsz - i;
    nperms *= perm_doms[i];
  }
  Cx::Table<uint> perm_vals(domsz-1);
  Cx::Table<uint> perm_map(domsz);

  for (luint perm_idx = 0; perm_idx < nperms; ++perm_idx) {
    state_of_index (&perm_vals[0], perm_idx, perm_doms);
    for (uint i = 0; i < domsz; ++i) {
      perm_map[i] = i;
    }
    for (uint i = 0; i < perm_vals.sz(); ++i) {
      SwapT( uint, perm_map[i], perm_map[i+perm_vals[i]] );
    }
    permute_pc_act(a, sub_a, perm_map);
    if (a.subseteq_ck(b)) {
      return true;
    }
  }
  return false;
}

  void
oput_uniring_invariant(Cx::OFile& ofile, const Cx::BitTable& actset, const uint domsz,
                       const char* pfx = "", const char* delim = " || ")
{
  UniAct prev( domsz );
  if (!delim)
    delim = pfx;

  Cx::Set< Cx::Tuple<uint, 2> > cache;
  for (zuint act_enum_idx = actset.begidx();
       act_enum_idx < actset.sz();
       act_enum_idx = actset.nextidx(act_enum_idx))
  {
    UniAct act = pc_act_of_enum_idx(act_enum_idx, domsz);
    act[2] = domsz;
    skip_unless (act != prev);
    ofile
      << pfx
      << "(x[i-1]==" << act[0]
      << " && x[i]==" << act[1] << ")"
      ;
    pfx = delim;
    prev = act;
  }
}

  void
oput_uniring_protocon_file(const Cx::String& ofilepath, const Cx::String& ofilename,
                           const Cx::BitTable& actset, const FilterOpt& opt)
{
  const uint domsz = opt.domsz;
  Cx::OFileB ofb;
  Cx::OFile ofile( ofb.uopen(ofilepath, ofilename) );

  ofile
    << "// " << actset
    << "\nconstant N := 3;"
    << "\nconstant M := " << domsz << ";"
    << "\nvariable x[Nat % N] <- Nat % M;"
    << "\nprocess P[i <- Nat % N]"
    << "\n{"
    << "\n  write: x[i];"
    << "\n  read: x[i-1];"
    << "\n  read: x[i+1];"
    << "\n  (future & silent)"
    << "\n    (0!=0"
    ;
  oput_uniring_invariant(ofile, actset, domsz, "\n     || ", 0);
  ofile << "\n    );";
  ofile << "\n}\n";
}

  void
recurse(BitTable set, uint q,
        Cx::Set<Cx::BitTable>& db,
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

    Cx::BitTable& db_elem = min_bt;

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
      UniAct act( val );
      set0_BitTable(set, enum_idx_of_pc_act(act, domsz));
    }
  }

  Cx::Set<Cx::BitTable> db;
  recurse(set, set.sz, db, opt, ofile);
  lose_BitTable (&set);
}

static void
oput_graphviz(Cx::OFile& ofile, const BitTable set, uint domsz)
{
#define NiceLooking
  ofile << "digraph G {\n"
    << " margin=0;\n"
    << " edge [weight=5];\n\n";

  for (zuint config_enum_idx = begidx_BitTable (set);
       config_enum_idx < set.sz;
       config_enum_idx = nextidx_BitTable (set, config_enum_idx))
  {
    UniAct config = pc_act_of_enum_idx(config_enum_idx, domsz);
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
    UniAct config_src = pc_act_of_enum_idx(config_enum_idx, domsz);
    biring_continuations(conts, config_enum_idx, set, domsz);

    Cx::Set< Cx::Tuple<uint, 2> > cache;
    for (uint i = 0; i < conts.sz(); ++i) {
#ifdef NiceLooking
      UniAct config_dst = pc_act_of_enum_idx(conts[i], domsz);
      Cx::Tuple<uint,2> dst_tup = mk_Tuple(config_dst[0], config_dst[1]);
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

static void
echo_subsets (const BitTable bt, const FilterOpt& opt, Cx::OFile& ofile)
{
  Cx::Set<Cx::BitTable> db;
  BitTable set = cons1_BitTable (bt.sz);

  for (zuint idx = begidx_BitTable (bt);
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
      if (opt.ppgck) {
        ofile << " ppg:" << (local_propagation_syn (set, domsz) ? 'Y' : 'N');
      }

      if (opt.echo_subsets) {
        echo_subsets(set, opt, ofile);
      }
      ofile << '\n';
    }

    if (opt.xlate_invariant) {
      oput_uniring_invariant (ofile, set, domsz, "", " || ");
      ofile << '\n';
    }
    if (opt.spec_ofilename) {
      oput_uniring_protocon_file("", opt.spec_ofilename, set, opt);
    }
    if (opt.graphviz_ofilename) {
      Cx::OFileB graphviz_ofileb;
      Cx::OFile graphviz_ofile( graphviz_ofileb.uopen(0, opt.graphviz_ofilename) );
      oput_graphviz(graphviz_ofile, set, domsz);
    }
  }

  lose_BitTable (&set);
}

int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);
  bool filter = false;
  FilterOpt opt;

  (void) subgraph_isomorphism_ck;

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

