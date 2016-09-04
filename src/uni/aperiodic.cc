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

#include "uniact.hh"
#include "unifile.hh"

#include "cx/alphatab.hh"
#include "cx/map.hh"
#include "cx/ofile.hh"
#include "cx/set.hh"
#include "cx/table.hh"


#include "../namespace.hh"
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
ReduceToActionTiles (Cx::Table<UniAct>& ret_acts, const Cx::Table< Cx::Tuple<uint,4> >& tiles)
{
  Cx::Map< Cx::Table<uint>, uint > idmap;
  Cx::Set<UniAct> acts;

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

    acts << UniAct( a0    , b1    , abcd  );
    acts << UniAct( blank , abcd  , c1    );
    acts << UniAct( abcd  , blank , d0    );
    acts << UniAct( c1    , d0    , blank );
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
  Cx::Table<UniAct> acts;
  const uint domsz = ReduceToActionTiles(acts, wtiles);

  Cx::OFile ofile(stdout_OFile ());
  if (eq_cstr ("-list", arg)) {
    for (uint i = 0; i < acts.sz(); ++i) {
      ofile.printf ("%3u %3u %3u\n", acts[i][0], acts[i][1], acts[i][2]);
    }
  }
  else if (eq_cstr ("-gv", arg)) {
    oput_graphviz(ofile, acts);
  }
  else if (eq_cstr ("-pml", arg)) {
    oput_promela(ofile, acts, domsz);
  }
  else if (eq_cstr ("-prot", arg)) {
    oput_protocon(ofile, acts, domsz);
  }

  lose_sysCx ();
  return 0;
}

END_NAMESPACE

int main(int argc, char** argv) {
  return PROJECT_NAMESPACE::main(argc, argv);
}
