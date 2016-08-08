/**
 * Convert a set of aperiodic Wang tiles to an aperiodic set of "action" tiles.
 * A set of action tiles has 2 properties:
 * 1. The tiles are SE-identical.
 *    - South and east edge colors are the same.
 * 2. The set is W-disabling.
 *    - No two tiles having the same west edge color
 *      can be placed directly above/below each other
 *      (i.e., the north color of one tile differs from
 *      the south color of the other tile, and vice-versa).
 *
 * This particular tile set is NW-deterministic, and therefore the action
 * tiles can be used to create a deterministic unidirectional ring protocol
 * that always terminates from any initial state on any ring size,
 * but it is quite hard to prove!
 *
 * This reduction is tweaked from my paper:
 *   "Verifying Livelock Freedom on Parameterized Rings and Chains"
 *   http://dx.doi.org/10.1007/978-3-319-03089-0_12
 * See the paper or tech report for details about problem significance,
 * but see the comment above ReduceToActionTiles() for the new reduction.
 * It will eventually appear in a journal version.
 *
 **/
extern "C" {
#include "cx/syscx.h"
}
#include "cx/synhax.hh"

#include "cx/alphatab.hh"
#include "cx/map.hh"
#include "cx/ofile.hh"
#include "cx/set.hh"
#include "cx/table.hh"
#include "cx/tuple.hh"

using Cx::mk_Tuple;

// Tile set originally from:
//   Grunbaum and Shephard's 1986 book "Tilings and Patterns".
// I pulled it from:
//   Hurd, Kari, and Culik's 1992 paper "The Topological Entropy of Cellular Automata is Uncomputable".
// It's also on Wikipedia as the size 16 set:
//   https://en.wikipedia.org/wiki/List_of_aperiodic_sets_of_tiles
// Edge colors are listed in order: west, north, south, east.
static const uint TileSet[][4] = {
//  W  N  S  E
  { 1, 1, 2, 2 },
  { 1, 5, 4, 1 },
  { 2, 3, 6, 2 },
  { 2, 4, 6, 1 },
  { 2, 5, 3, 1 },
  { 3, 2, 2, 6 },
  { 3, 3, 4, 4 },
  { 3, 4, 4, 5 },
  { 3, 6, 4, 3 },
  { 4, 2, 1, 6 },
  { 4, 3, 5, 4 },
  { 4, 4, 5, 5 },
  { 5, 1, 1, 4 },
  { 5, 2, 1, 3 },
  { 6, 3, 3, 4 },
  { 6, 6, 3, 3 }
};

/** Lookup/create a unique id for a symbol.
 *
 * A symbol is an array of color values from the input Wang tile set.
 **/
static
  uint
LookupSymId (Cx::Map< Cx::Table<uint>, uint >& idmap, const Cx::Table<uint>& key)
{
  return idmap.ensure(key, idmap.sz());
}

/** Populate {ret_acts}, return domain size.
 *
 * Each input Wang tile is converted to some action tiles by the following transformation:
 *                     ________ ________
 *                    |   b1   |    $   |
 *    ________        |        |        |
 *   |    b   |       |a0  abcd|abcd  d0|
 *   |        |       |        |        |
 *   |a      d|  -->  |__abcd__|___d0___|
 *   |        |       |  abcd  |   d0   |
 *   |____c___|       |        |        |
 *                    |$     c1|c1     $|
 *                    |        |        |
 *                    |___c1___|____$___|
 **/
static
  uint
ReduceToActionTiles (Cx::Table< Cx::Tuple<uint,3> >& ret_acts, const Cx::Table< Cx::Tuple<uint,4> >& tiles)
{
  Cx::Map< Cx::Table<uint>, uint > idmap;
  Cx::Set< Cx::Tuple<uint,3> > acts;

  // This is the $ symbol.
  const uint blank = LookupSymId (idmap, Cx::Table<uint>());

  // Reserve low symbol ids (i.e., action tile colors) in the action tile set
  // for those corresponding to Wang tile colors.
  {
    Cx::Set<uint> ri_colors, up_colors;
    for (uint tile_idx = 0; tile_idx < tiles.sz(); ++tile_idx) {
      const Cx::Tuple<uint,4>& tile = tiles[tile_idx];
      up_colors << tile[0] << tile[3];
      ri_colors << tile[1] << tile[2];
    }
    Cx::Set<uint>::const_iterator it;
    for (it = ri_colors.begin(); it != ri_colors.end(); ++it) {
      Cx::Table<uint> sym;
      LookupSymId (idmap, (sym << *it << 0));
    }
    for (it = up_colors.begin(); it != up_colors.end(); ++it) {
      Cx::Table<uint> sym;
      LookupSymId (idmap, (sym << *it << 1));
    }
  }

  for (uint tile_idx = 0; tile_idx < tiles.sz(); ++tile_idx) {
    const Cx::Tuple<uint,4>& tile = tiles[tile_idx];
    Cx::Table<uint> sym;

    sym << tile[0] << tile[1] << tile[2] << tile[3];
    const uint abcd = LookupSymId (idmap, sym);

    sym.flush() << tile[0] << 0;
    const uint a0 = LookupSymId (idmap, sym);

    sym.flush() << tile[1] << 1;
    const uint b1 = LookupSymId (idmap, sym);

    sym.flush() << tile[2] << 1;
    const uint c1 = LookupSymId (idmap, sym);

    sym.flush() << tile[3] << 0;
    const uint d0 = LookupSymId (idmap, sym);

    acts << mk_Tuple( a0    , b1    , abcd  );
    acts << mk_Tuple( blank , abcd  , c1    );
    acts << mk_Tuple( abcd  , blank , d0    );
    acts << mk_Tuple( c1    , d0    , blank );
  }
  acts.fill(ret_acts);
  return idmap.sz();
}

/** Execute me now!**/
int main (int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);
  const char* arg = argv[argi];

  if (argi+1 != argc || eq_cstr("-h", arg)) {
    failout_sysCx ("Expect one argument of: -gv, -list, -pml, -prot");
    return 1;
  }

  Cx::Table< Cx::Tuple<uint,4> > wtiles;
  for (uint i = 0; i < ArraySz(TileSet); ++i) {
    const uint* t = TileSet[i];
    wtiles << mk_Tuple(t[0], t[1], t[2], t[3]);
  }

  // Compute equivalent action tiles.
  Cx::Table< Cx::Tuple<uint,3> > acts;
  const uint domsz = ReduceToActionTiles(acts, wtiles);

  Cx::OFile ofile(stdout_OFile ());
  if (eq_cstr ("-list", arg)) {
    for (uint i = 0; i < acts.sz(); ++i) {
      ofile.printf ("%3u %3u %3u\n", acts[i][0], acts[i][1], acts[i][2]);
    }
  }
  else if (eq_cstr ("-gv", arg)) {
    Cx::Map<Cx::Tuple<uint,2>, Cx::String> edges;
    for (uint i = 0; i < acts.sz(); ++i) {
      edges[mk_Tuple(acts[i][0], acts[i][2])].push_delim("|") << acts[i][1];
    }

    ofile << "digraph {";
    Cx::Map<Cx::Tuple<uint,2>, Cx::String>::const_iterator it;
    for (it = edges.begin(); it != edges.end(); ++it) {
      const Cx::Tuple<uint,2> edge = it->first;
      const Cx::String label = it->second;
      ofile.printf ("\n  %3u -> %3u [label = \"%s\"];", edge[0], edge[1], label.ccstr());
    }
    ofile << "\n}\n";
  }
  else if (eq_cstr ("-pml", arg)) {
    ofile
      << "// Promela file. For better quality, use Protocon to create this."
      << "\n#define N 4"
      << "\nbyte x[N];"
      << "\nbyte initializing = N;"
      << "\n#define x_sc x[(_pid+N-1)%N]"
      << "\n#define x_id x[_pid]"
      << "\n#define UniAct(a,b,c)  atomic { (x_sc == a) && (x_id == b) -> x_id = c; }"
      << "\nactive[N] proctype P()"
      << "\n{"
      << "\n  atomic {"
      << "\n    byte tmp;"
      ;
    ofile.printf("\n    select(tmp : 0..%u);", domsz-1);
    ofile
      << "\n    x_id = tmp;"
      << "\n    initializing --;"
      << "\n  }"
      << "\n  (initializing==0);"
      << "\nend_P:"
      << "\n  do"
      ;

    for (uint i = 0; i < acts.sz(); ++i) {
      ofile.printf ("\n  :: UniAct( %3u, %3u, %3u )",
                    acts[i][0], acts[i][1], acts[i][2]);
    }
    ofile
      << "\n  od;"
      << "\n}\n"
      ;
  }
  else if (eq_cstr ("-prot", arg)) {
    ofile
      << "// Protocon file."
      << "\nconstant N := 3;"
      ;
    ofile.printf ("\nconstant M := %u;", domsz);
    ofile.printf ("\nconstant NActs := %u;", acts.sz());
    for (uint abc = 0; abc < 3; ++abc) {
      ofile << "\nconstant " << (char)('a' + abc) << " := ( ";
      for (uint i = 0; i < acts.sz(); ++i) {
        if (i > 0)  ofile << ", ";
        ofile << acts[i][abc];
      }
      ofile << " );";
    }

    ofile
      << "\nvariable x[Nat % N] <- Nat % M;"
      << "\nprocess P[i <- Nat % N]"
      << "\n{"
      << "\n  read: x[i-1];"
      << "\n  write: x[i];"
      << "\n  (future & silent)"
      << "\n    (forall j <- Nat % NActs : !(x[i-1]==a[j] && x[i]==b[j]));"
      << "\n  puppet:"
      ;
    for (uint i = 0; i < acts.sz(); ++i) {
      ofile.printf ("\n    ( x[i-1]==a[%u] && x[i]==b[%u] --> x[i]:=c[%u]; )", i, i, i);
    }
    ofile
      << "\n    ;"
      << "\n}\n";
  }

  lose_sysCx ();
  return 0;
}

