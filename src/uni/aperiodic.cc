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
 **/
#include <iostream>

#include <fildesh/fildesh.h>

#include "src/cx/map.hh"
#include "src/cx/set.hh"
#include "src/cx/table.hh"
#include "src/uni/uniact.hh"

#include "src/namespace.hh"

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
LookupSymId (Map< Triple<uint>, uint >& idmap,
             const uint v0 = UINT_MAX,
             const uint v1 = UINT_MAX,
             const uint v2 = UINT_MAX)
{
  return idmap.ensure(Triple<uint>(v0, v1, v2), idmap.sz());
}

/** Populate {ret_acts}, return domain size.
 *
 * Each input Wang tile is converted to some action tiles by the following transformation:
 *                     ________ ________
 *                    |   b1   |    $   |
 *    ________        |        |        |
 *   |    b   |       |a0    cd|cd    d0|
 *   |        |       |        |        |
 *   |a      d|  -->  |___cd___|___d0___|
 *   |        |       |   cd   |   d0   |
 *   |____c___|       |        |        |
 *                    |$     c1|c1     $|
 *                    |        |        |
 *                    |___c1___|____$___|
 **/
static
  uint
ReduceToActionTiles (Table<UniAct>& ret_acts, const Table< Tuple<uint,4> >& tiles)
{
  Map< Triple<uint>, uint > idmap;
  Set<UniAct> acts;

  const uint doll = LookupSymId(idmap);
  const uint direction_tag = 1;

  // Reserve low symbol ids (i.e., action tile colors) in the action tile set
  // for those corresponding to Wang tile colors.
  {
    Set<uint> ri_colors, up_colors;
    for (uint tile_idx = 0; tile_idx < tiles.sz(); ++tile_idx) {
      const Tuple<uint,4>& tile = tiles[tile_idx];
      ri_colors << tile[0] << tile[3];
      up_colors << tile[1] << tile[2];
    }
    Set<uint>::const_iterator it;
    for (it = ri_colors.begin(); it != ri_colors.end(); ++it) {
      LookupSymId(idmap, *it, 0, direction_tag);
    }
    for (it = up_colors.begin(); it != up_colors.end(); ++it) {
      LookupSymId(idmap, *it, 1, direction_tag);
    }
  }


  for (uint tile_idx = 0; tile_idx < tiles.sz(); ++tile_idx) {
    const Tuple<uint,4>& tile = tiles[tile_idx];

    const uint
        cd = LookupSymId(idmap, tile[2], tile[3])
      , a0 = LookupSymId(idmap, tile[0], 0, direction_tag)
      , b1 = LookupSymId(idmap, tile[1], 1, direction_tag)
      , c1 = LookupSymId(idmap, tile[2], 1, direction_tag)
      , d0 = LookupSymId(idmap, tile[3], 0, direction_tag)
      ;

    acts
      << UniAct( a0   , b1   , cd    )
      << UniAct( doll , cd   , c1    )
      << UniAct( cd   , doll , d0    )
      << UniAct( c1   , d0   , doll  )
      ;
  }
  acts.fill(ret_acts);
  return idmap.sz();
}

/** Populate {ret_acts}, return domain size.
 *
 * Each input Wang tile is converted to some
 * commutative action tiles by the following transformation:
 *                     ________ ________ ________
 *                    |   b1   |   00   |    $   |
 *                    |        |        |        |
 *                    |a0    cd|cd   d00|d00   d0|
 *                    |        |        |        |
 *    ________        |___cd___|___d00__|___d0___|
 *   |    b   |       |   cd   |   d00  |   d0   |
 *   |        |       |        |        |        |
 *   |a      d|  -->  |11   c11|c11    #|#     11|
 *   |        |       |        |        |        |
 *   |____c___|       |___c11__|____#___|___11___|
 *                    |   c11  |    #   |   11   |
 *                    |        |        |        |
 *                    |$     c1|c1    00|00     $|
 *                    |        |        |        |
 *                    |___c1___|___00___|____$___|
 **/
static
  uint
ReduceToCommutativeTiles(Table<UniAct>& ret_acts,
                         const Table< Tuple<uint,4> >& tiles)
{
  Map< Triple<uint>, uint > idmap;
  Set<UniAct> acts;

  const uint special_tag = 0;
  const uint direction_tag = 1;
  const uint double_direction_tag = 2;

  const uint id00 = LookupSymId(idmap, 0, 0, special_tag);
  const uint id11 = LookupSymId(idmap, 1, 0, special_tag);
  const uint hash = LookupSymId(idmap, 3, 0, special_tag);
  const uint doll = LookupSymId(idmap, 2, 0, special_tag);

  for (uint tile_idx = 0; tile_idx < tiles.sz(); ++tile_idx) {
    const Tuple<uint,4>& tile = tiles[tile_idx];
    const uint a = tile[0],  b = tile[1],  c = tile[2],  d = tile[3];

    const uint
        cd  = LookupSymId(idmap, c, d)
      , a0  = LookupSymId(idmap, a, 0, direction_tag)
      , d0  = LookupSymId(idmap, d, 0, direction_tag)
      , d00 = LookupSymId(idmap, d, 0, double_direction_tag)
      , b1  = LookupSymId(idmap, b, 1, direction_tag)
      , c1  = LookupSymId(idmap, c, 1, direction_tag)
      , c11 = LookupSymId(idmap, c, 1, double_direction_tag)
      ;

#define ReductionTile(x, y, z) \
    UniAct(x, y, z) << UniAct(y, x, z)

#define ReductionRow(t, u, v, w, x, y, z) \
    ReductionTile(t, u, v) << ReductionTile(v, w, x) << ReductionTile(x, y, z)

    acts
      << ReductionRow(  a0,  b1,  cd, id00,  d00, doll,   d0)
      << ReductionRow(id11,  cd, c11,  d00, hash,   d0, id11)
      << ReductionRow(doll, c11,  c1, hash, id00, id11, doll)
      ;
#undef ReductionRow
#undef ReductionTile
  }
  acts.fill(ret_acts);
  return idmap.sz();
  return idmap.sz();
}


static bool
check_constraints(Table<UniAct>& acts, bool commutative)
{
  const bool explain_failure = true;
  Set<UniAct> actset(acts);
  Set< Tuple<PcState,2> > guardset;


#define ExplainFail(s) \
do { \
  if (explain_failure) \
    DBog4("%s: (%u, %u, %u)", s, (uint)a, (uint)b, (uint)c); \
  return false; \
} while (false)

  for (uint i = 0; i < acts.sz(); ++i) {
    const UniAct& act = acts[i];
    const PcState a = act[0],  b = act[1],  c = act[2];

    Tuple<PcState,2> guard = mk_Tuple(a, b);
    if (guardset.elem_ck(guard))
      ExplainFail("Not deterministic");
    guardset << guard;
  }


  for (uint i = 0; i < acts.sz(); ++i) {
    const UniAct& act = acts[i];
    const PcState a = act[0],  b = act[1],  c = act[2];

    if (guardset.elem_ck(mk_Tuple(a, c)))
      ExplainFail("Not W-disabling");

    if (guardset.elem_ck(mk_Tuple(c, b)))
      ExplainFail("Not N-disabling");

    if (commutative && !actset.elem_ck(UniAct(b, a, c)))
      ExplainFail("Not commutative");
  }

#undef ExplainFail
  return true;
}

/** Execute me now!**/
int main (int argc, char** argv)
{
  int argi = 1;
  const char* arg = argv[argi];

  bool commutative = false;
  if (arg &&
      (0 == strcmp(arg, "-commute") ||
       0 == strcmp(arg, "-commutative")))
  {
    arg = argv[++argi];
    commutative = true;
  }

  Table< Tuple<uint,4> > wtiles;
  for (uint i = 0; i < ArraySz(TileSet); ++i) {
    const uint* t = TileSet[i];
    wtiles << mk_Tuple(t[0], t[1], t[2], t[3]);
  }

  // Compute equivalent action tiles.
  Table<UniAct> acts;
  const uint domsz =
    commutative
    ? ReduceToCommutativeTiles(acts, wtiles)
    : ReduceToActionTiles(acts, wtiles);
  assert(domsz > 0);

  if (!check_constraints(acts, commutative)) {
    fildesh_log_error("Reduction does not preserve good properties.");
    return 1;
  }

  for (unsigned i = 0; i < acts.size(); ++i) {
    std::cout << acts[i][0] << '\t' << acts[i][1] << '\t' << acts[i][2] << '\n';
  }
  return 0;
}

END_NAMESPACE

int main(int argc, char** argv) {
  return PROTOCON_NAMESPACE::main(argc, argv);
}
