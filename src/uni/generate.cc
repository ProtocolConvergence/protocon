
extern "C" {
#include "cx/syscx.h"
}

#include <algorithm>
#include "cx/fileb.hh"
#include "cx/map.hh"
#include "cx/table.hh"
#include "cx/bittable.hh"
#include "cx/set.hh"
#include "uniact.hh"
#include "adjlist.hh"

#include "../namespace.hh"

#define each_in_BitTable(i , bt) \
  (zuint i = bt.begidx(); i < bt.sz(); bt.nextidx(&i))

#define UseNaturalOrder

namespace C {
  using Cx::C::OFile;
  using Cx::C::XFile;
}

using Cx::OFileB;
using Cx::mk_Tuple;
using Cx::Triple;

struct FilterOpt
{
  uint domsz;
  uint max_depth;
  uint minsz;
  bool echo_bits;
  bool count_ones;
  bool xlate_invariant;
  const char* prot_ofilename;
  const char* graphviz_ofilename;

  FilterOpt()
    : domsz( 3 )
    , max_depth( 0 )
    , minsz( 3 )
    , echo_bits( false )
    , count_ones( false )
    , xlate_invariant( false )
    , prot_ofilename( 0 )
    , graphviz_ofilename( 0 )
  {}
};


OFile& operator<<(OFile& of, const BitTable& bt)
{
  for (zuint i = 0; i < bt.sz(); ++i)
    of << bt[i];
  return of;
}

  bool
minimal_unique_ck (const uint* a, uint n)
{
  BitTable hits(n, 0);

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
  uint
addmod (uint a, uint b, uint n)
{
  return (a + b) % n;
}

static inline
  uint
submod (uint a, uint b, uint n)
{
  return (a + n - b) % n;
}

static inline
  UniAct
act_of_id(uint actid, const uint domsz)
{
#ifdef UseNaturalOrder
  const div_t lo = div(actid, domsz);
  const div_t hi = div(lo.quot, domsz);
  return UniAct(hi.quot, hi.rem, lo.rem);
#else
  const div_t lo = div(actid, domsz);
  const div_t hi = div(lo.quot, domsz);
  const uint c = lo.rem;
  const uint b = submod(hi.rem, c, domsz);
  const uint a = submod(hi.quot, b, domsz);
  return UniAct(a, b, c);
#endif
}

static inline
  uint
id_of2(uint a, uint b, uint domsz)
{
  Claim( a < domsz );
  Claim( b < domsz );
  return a * domsz + b;
}

static inline
  uint
id_of3(uint a, uint b, uint c, uint domsz)
{
  Claim( a < domsz );
  Claim( b < domsz );
  Claim( c < domsz );
#ifdef UseNaturalOrder
  return (a * domsz + b) * domsz + c;
#else
  return (addmod(a, b, domsz) * domsz + addmod(b, c, domsz)) * domsz + c;
#endif
}

static inline uint id_of(const Tuple<uint,2>& u, const uint domsz)
{ return id_of2(u[0], u[1], domsz); }

static inline uint id_of(const Tuple<uint,3>& u, const uint domsz)
{ return id_of3(u[0], u[1], u[2], domsz); }

  void
permute_pc_act (BitTable& bt, const BitTable& set, const Table<uint>& perm_map)
{
  const uint domsz = perm_map.sz();
  bt.wipe(0);
  for each_in_BitTable(actid , set) {
    UniAct act = act_of_id(actid, domsz);;
    for (uint j = 0; j < 3; ++j) {
      act[j] = perm_map[act[j]];
    }
    bt.set1(id_of(act, domsz));
  }
}

  void
del_node(AdjList<uint>& digraph, AdjList<uint>& rdigraph, uint node_id)
{
  {
    const uint* dsts = digraph.arcs_from(node_id);
    const uint ndsts = digraph.degree(node_id);
    for (uint i = 0; i < ndsts; ++i)
      rdigraph.del_arc(dsts[i], node_id);
  }
  {
    const uint* srcs = rdigraph.arcs_from(node_id);
    const uint nsrcs = rdigraph.degree(node_id);
    for (uint i = 0; i < nsrcs; ++i)
      digraph.del_arc(srcs[i], node_id);
  }
  digraph.del_arcs_from(node_id);
}

static
  void
subtract_action_mask(BitTable& mask, const UniAct& mask_act, uint domsz)
{
  UniAct beg( 0, 0, 0 );
  UniAct inc( 1, 1, 1 );

  for (uint i = 0; i < 3; ++i) {
    skip_unless (mask_act[i] != domsz);
    beg[i] = mask_act[i];
    inc[i] = domsz;
  }

  for (uint a = beg[0]; a < domsz; a += inc[0]) {
    for (uint b = beg[1]; b < domsz; b += inc[1]) {
      for (uint c = beg[2]; c < domsz; c += inc[2]) {
        mask.set0(id_of3(a, b, c, domsz));
      }
    }
  }
}

inline
  bool
action_mask_overlap_ck(const UniAct& mask_act, const BitTable& actset, uint domsz)
{
  UniAct beg( 0, 0, 0 );
  UniAct inc( 1, 1, 1 );

  for (uint i = 0; i < 3; ++i) {
    skip_unless (mask_act[i] != domsz);
    beg[i] = mask_act[i];
    inc[i] = domsz;
  }

  for (uint a = beg[0]; a < domsz; a += inc[0]) {
    for (uint b = beg[1]; b < domsz; b += inc[1]) {
      for (uint c = beg[2]; c < domsz; c += inc[2]) {
        if (actset.ck(id_of(UniAct(a, b, c), domsz))) {
          return true;
        }
      }
    }
  }
  return false;
}

  Trit
livelock_semick_rec(const Table<uint>& top_row,
                    uint mid_west,
                    const Table< Tuple<uint,2> >& match_row,
                    uint limit,
                    const Table<uint>& ppgfun,
                    uint domsz,
                    BitTable& livelockset)
{
  Table<uint> mid_row;
  {
    const uint c = ppgfun[id_of2(mid_west, top_row[0], domsz)];
    if (c >= domsz)
      return Nil;

    mid_row.affysz(top_row.sz());
    mid_row[0] = c;
  }

  for (uint i = 1; i < top_row.sz(); ++i) {
    const uint a = mid_row[i-1];
    const uint b = top_row[i];
    const uint c = ppgfun[id_of2(a, b, domsz)];
    if (c >= domsz)
      return Nil;
    mid_row[i] = c;
  }
  if (mid_row.top() != mid_west)
    return May;

  bool match = true;
  for (uint i = 0; i < mid_row.sz(); ++i) {
    if (mid_row[i] != match_row[i][1]) {
      match = false;
      break;
    }
  }
  if (match)
    return Yes;

  if (limit == 0)
    return May;

  bool impossible = true;
  for (uint bot_west = 0; bot_west < domsz; ++bot_west) {
    const Trit livelock_exists =
      livelock_semick_rec(mid_row, bot_west,
                          match_row, limit-1,
                          ppgfun, domsz, livelockset);
    if (livelock_exists == Yes) {
      for (uint i = 0; i < mid_row.sz(); ++i) {
        const uint a = (i == 0 ? mid_west : mid_row[i-1]);
        const uint b = top_row[i];
        const uint c = mid_row[i];
        const uint actid = id_of3(a, b, c, domsz);
        livelockset.set1(actid);
      }
      return Yes;
    }
    impossible = impossible && (livelock_exists == Nil);
  }
  return (impossible ? Nil : May);
}

  bool
livelock_ck(const Table< Tuple<uint,2> >& acts, const Table<uint>& ppgfun,
            const uint domsz, BitTable& livelockset)
{
  livelockset.wipe(0);
  const uint limit = domsz * domsz;
  Table<uint> top_row;
  top_row.affysz(acts.sz());
  for (uint i = 0; i < acts.sz(); ++i) {
    const PcState a = acts[i][0];
    const PcState b = acts[i][1];
    const PcState c = ppgfun[id_of2(a, b, domsz)];
    top_row[i] = c;
    livelockset.set1(id_of3(a, b, c, domsz));
  }

  for (uint mid_west = 0; mid_west < domsz; ++mid_west) {
    const Trit livelock_exists =
      livelock_semick_rec(top_row, mid_west,
                          acts, limit-1,
                          ppgfun, domsz, livelockset);
    if (livelock_exists == Yes)
      return true;
  }
  return false;
}

  bool
cycle_ck_from(uint initial_node, const AdjList<uint>& digraph, Table< Tuple<uint,2> >& stack,
              BitTable& visited)
{
  if (digraph.degree(initial_node) == 0) {
    return false;
  }
  stack.flush();
  visited.wipe(0);

  stack << mk_Tuple<uint>(initial_node, 0);
  while (!stack.empty_ck()) {
    uint x = stack.top()[0];
    bool backtrack = true;
    for (uint i = stack.top()[1]; i < digraph.degree(x); ++i) {
      uint y = digraph.arc_from(x, i);
      skip_unless (!visited.set1(y));
      stack.top()[1] = i+1;
      stack << mk_Tuple<uint>(y, 0);
      backtrack = false;
      break;
    }
    if (backtrack) {
      stack.cpop();
    }
    else if (stack.top()[0] == initial_node) {
      stack.cpop();
      break;
    }
  }
  return !stack.empty_ck();
}

  Trit
periodic_leads_semick(const BitTable& delegates,
                      uint domsz, BitTable& mask,
                      Table<BitTable>& candidates_stack,
                      const uint depth)
{
  Table<PcState> ppgfun;
  ppgfun.affysz(domsz*domsz, domsz);

  for each_in_BitTable(actid , delegates) {
    UniAct act = act_of_id(actid, domsz);
    ppgfun[id_of2(act[0], act[1], domsz)] = act[2];
  }

  AdjList<uint> digraph( domsz*domsz*domsz );
  // Create an arc from node (a,b,d) to node (c,e,g)
  // whenever the following action tiles exist:
  //
  //  * *
  // *+b+e  top:    (*,*,b), (b,*,e)
  //  b e
  // a+c+f  middle: (a,b,c), (c,e,f)
  //  c f
  // *+d+g  bottom: (*,c,d), (d,f,g)
  //  d g
  //
  // No existence check is needed for (*,*,b) or (*,c,d),
  // but we do check for (*,c,d) because it makes the graph cleaner.
  DoTwice(digraph.commit_degrees()) {
    for each_in_BitTable(actid , delegates) {
      const UniAct mid_act = act_of_id(actid, domsz);
      const PcState a = mid_act[0], b = mid_act[1], c = mid_act[2];

      for (PcState d = 0; d < domsz; ++d) {
        const UniAct bot_mask_act(domsz, b, d);
        skip_unless (action_mask_overlap_ck(bot_mask_act, delegates, domsz));
        const Triple<PcState> node(a, b, d);
        const uint node_id = id_of(node, domsz);

        for (PcState e = 0; e < domsz; ++e) {
          // Ensure next middle tile exists.
          const PcState f = ppgfun[id_of2(c, e, domsz)];
          skip_unless (f < domsz);
          // Ensure next bottom tile exists.
          const PcState g = ppgfun[id_of2(d, f, domsz)];
          skip_unless (g < domsz);
          // Ensure next top tile exists.
          const UniAct next_top_mask_act = UniAct(b, domsz, e);
          skip_unless (action_mask_overlap_ck(next_top_mask_act, delegates, domsz));
          // Add arc from this node to the next.
          const Triple<PcState> next(c, e, g);
          const uint next_id = id_of(next, domsz);
          digraph.add_arc(node_id, next_id);
        }
      }
    }
  }

  const BitTable& candidates = candidates_stack[depth];
  mask = delegates;
  mask |= candidates;

  AdjList<uint> overapprox_digraph( digraph.nnodes() );
  DoTwice(overapprox_digraph.commit_degrees()) {
    for each_in_BitTable(actid , mask) {
      const UniAct mid_act = act_of_id(actid, domsz);
      const PcState a = mid_act[0], b = mid_act[1], c = mid_act[2];

      for (PcState d = 0; d < domsz; ++d) {
        const UniAct bot_mask_act(domsz, b, d);
        skip_unless (action_mask_overlap_ck(bot_mask_act, mask, domsz));
        const Triple<PcState> node(a, b, d);
        const uint node_id = id_of(node, domsz);

        for (PcState e = 0; e < domsz; ++e) {
          // Ensure next top tile exists.
          const UniAct next_top_mask_act = UniAct(b, domsz, e);
          skip_unless (action_mask_overlap_ck(next_top_mask_act, mask, domsz));

          for (PcState f = 0; f < domsz; ++f) {
            // Ensure next middle tile exists.
            skip_unless (mask.ck(id_of3(c, e, f, domsz)));

            for (PcState g = 0; g < domsz; ++g) {
              // Ensure next bottom tile exists.
              skip_unless (mask.ck(id_of3(d, f, g, domsz)));

              // Add arc from this node to the next.
              const Triple<PcState> next(c, e, g);
              const uint next_id = id_of(next, domsz);
              overapprox_digraph.add_arc(node_id, next_id);
            }
          }
        }
      }
    }
  }

  BitTable pending = delegates;
  Table< Tuple<uint,2> > stack;

  bool all = true;
  for each_in_BitTable(actid , pending) {
    const UniAct act = act_of_id(actid, domsz);
    bool found = false;
    // Find all starting nodes.
    for (PcState d = 0; d < domsz; ++d) {
      const uint node_id = id_of3(act[0], act[1], d, domsz);
      skip_unless (cycle_ck_from(node_id, digraph, stack, mask));
      found = true;
      break;
    }

    if (!found) {
      all = false;
      for (PcState d = 0; d < domsz; ++d) {
        const uint node_id = id_of3(act[0], act[1], d, domsz);
        skip_unless (cycle_ck_from(node_id, overapprox_digraph, stack, mask));
        found = true;
        break;
      }
      if (!found) {
        return Nil;
      }
      continue;
    }

    for (uint i = 0; i < stack.sz(); ++i) {
      Triple<uint> node = act_of_id(stack[i][0], domsz);
      const PcState a = node[0];
      const PcState b = node[1];
      const PcState c = ppgfun[id_of2(a, b, domsz)];
      Claim( c < domsz );
      pending.set0(id_of3(a, b, c, domsz));

      // Change this stack to more easily represent the livelock.
      stack[i][0] = a;
      stack[i][1] = b;
    }
    if (livelock_ck(stack, ppgfun, domsz, mask)) {
      uint max_livelock_actids[2] = { 0, 0 };
      for each_in_BitTable( livelock_actid , mask ) {
        max_livelock_actids[0] = max_livelock_actids[1];
        max_livelock_actids[1] = livelock_actid;
      }
      // We should never have a self-loop livelock.
      Claim( max_livelock_actids[0] > 0 );
      for (uint i = 0; i < depth; ++i) {
        if (!candidates_stack[i].ck(max_livelock_actids[1])) {
          candidates_stack[i].wipe(0);
        }
        else if (!candidates_stack[i].ck(max_livelock_actids[0])) {
          // If the penultimate livelock action is picked,
          // forbid the maximal livelock action.
          candidates_stack[i].set0(max_livelock_actids[1]);
        }
      }
      return Nil;
    }
  }

  return (all ? Yes : May);
}

  bool
canonical_ck(const BitTable& set, const uint domsz, BitTable& bt)
{
  Table<uint> perm_doms(domsz-1);
  luint nperms = 1;
  for (uint i = 2; i <= domsz; ++i) {
    perm_doms[i-2] = i;
    nperms *= perm_doms[i-2];
  }
  Table<uint> perm_vals(domsz-1);
  Table<uint> perm_map(domsz);

  for (luint perm_idx = 0; perm_idx < nperms; ++perm_idx) {
    state_of_index (&perm_vals[0], perm_idx, perm_doms);
    for (uint i = 0; i < domsz; ++i) {
      perm_map[i] = i;
    }
    for (uint i = 0; i < perm_vals.sz(); ++i) {
      SwapT( uint, perm_map[i], perm_map[perm_vals[i]] );
    }
    Claim( minimal_unique_ck(&perm_map[0], perm_map.sz()) );
    permute_pc_act (bt, set, perm_map);
    if (bt > set) {
      return false;
    }
  }
  return true;
}

  void
trim_coexist (BitTable& actset, uint actid, uint domsz)
{
  UniAct act( act_of_id(actid, domsz) );

  // Trivial livelock.
  if (act[0]==act[1]) {
    subtract_action_mask(actset, UniAct(act[2], act[2], act[0]), domsz);
  }

  // Trivial livelock.
  if (act[0]==act[2]) {
    subtract_action_mask(actset, UniAct(act[1], act[0], act[1]), domsz);
  }

  // Enforce determinism.
  subtract_action_mask(actset, UniAct(act[0], act[1], domsz), domsz);
  //mask.set0(actid);

  // Enforce W-disabling.
  subtract_action_mask(actset, UniAct(act[0], act[2], domsz), domsz);
  subtract_action_mask(actset, UniAct(act[0], domsz, act[1]), domsz);

#if 0
  // Enforce N-disabling?
  subtract_action_mask(actset, UniAct(act[2], act[1], domsz), domsz);
  subtract_action_mask(actset, UniAct(domsz, act[1], act[0]), domsz);
#endif
}

  void
recurse(Table<BitTable>& delegates_stack,
        Table<BitTable>& candidates_stack,
        uint actid,
        const FilterOpt& opt, OFile& ofile,
        uint depth,
        uint max_depth,
        BitTable& mask)
{
  const uint domsz = opt.domsz;

  BitTable& delegates = delegates_stack[depth];
  BitTable& candidates = candidates_stack[depth];

  delegates = delegates_stack[depth-1];
  candidates = candidates_stack[depth-1];

  Claim( candidates.ck(actid) );
  delegates.set1(actid);
  candidates.set0(actid);
  trim_coexist(candidates, actid, domsz);

  bool print_delegates = true;
  switch (periodic_leads_semick(delegates, domsz, mask, candidates_stack, depth)) {
    case Nil: return;
    case May: print_delegates = false;
    case Yes: break;
  }
  if (!canonical_ck(delegates, domsz, mask)) {
    return;
  }
  if (print_delegates) {
    ofile << delegates << '\n';
    ofile.flush();
  }
  if (depth == max_depth)
    return;

  for (uint next_actid = actid+1; next_actid < candidates.sz(); ++next_actid) {
    skip_unless (candidates.ck(next_actid));
    recurse(delegates_stack, candidates_stack,
            next_actid, opt, ofile, depth+1, max_depth, mask);

    // This must be after recurse() so that the livelock
    // detection doesn't remove valid candidates.
    candidates.set0(next_actid);
  }
}

  void
searchit(const FilterOpt& opt, OFile& ofile)
{
  const uint domsz = opt.domsz;
  const uint max_depth =
    (opt.max_depth > 0 ? opt.max_depth : domsz*domsz);

  Table<BitTable> delegates_stack;
  Table<BitTable> candidates_stack;

  BitTable mask( domsz*domsz*domsz, 0 );
  delegates_stack.affysz( max_depth+1, mask );

  mask.wipe(1);
  candidates_stack.affysz( max_depth+1, mask );

  BitTable& candidates = candidates_stack[0];
  uint actid;

  // Remove self-loops.
  for (uint a = 0; a < domsz; ++a) {
    for (uint b = 0; b < domsz; ++b) {
      candidates.set0(id_of3(a, b, b, domsz));
    }
  }

#define RECURSE \
  recurse(delegates_stack, candidates_stack, actid, opt, ofile, 1, max_depth, mask)

#ifdef UseNaturalOrder
  actid = id_of3(0, 0, 1, domsz);
  RECURSE;

  // Remove all (a, a, b) actions.
  for (uint a = 0; a < domsz; ++a) {
    for (uint b = 0; b < domsz; ++b) {
      candidates.set0(id_of3(a, a, b, domsz));
    }
  }

  actid = id_of3(0, 1, 0, domsz);
  RECURSE;

  // Remove all (a, b, a) actions.
  for (uint a = 0; a < domsz; ++a) {
    for (uint b = 0; b < domsz; ++b) {
      candidates.set0(id_of3(a, b, a, domsz));
    }
  }

  actid = id_of3(0, 1, 2, domsz);
  RECURSE;
#else
  for (actid = 0; actid < candidates.sz(); ++actid) {
    skip_unless( candidates.ck(actid) );
    RECURSE;
  }
#endif

#undef RECURSE
}

  void
oput_uniring_invariant(OFile& ofile, const BitTable& set, const uint domsz,
                       const char* pfx = "", const char* delim = " || ")
{
  UniAct prev( domsz );
  if (!delim)
    delim = pfx;

  Set< Tuple<uint, 2> > cache;
  for each_in_BitTable(actid , set) {
    UniAct act = act_of_id(actid, domsz);
    act[2] = domsz;
    skip_unless (act != prev);
    ofile
      << pfx
      << "!(x[i-1]==" << act[0]
      << " && x[i]==" << act[1] << ")"
      ;
    pfx = delim;
    prev = act;
  }
}

  void
oput_uniring_protocon_file(const String& ofilepath, const String& ofilename,
                           const BitTable& actset, const FilterOpt& opt)
{
  const uint domsz = opt.domsz;
  OFileB ofb;
  OFile ofile( ofb.uopen(ofilepath, ofilename) );

  ofile
    << "// " << actset
    << "\nconstant N := 3;"
    << "\nconstant M := " << domsz << ";"
    << "\nvariable x[N] < M;"
    << "\nprocess P[i < N]"
    << "\n{"
    << "\n  read: x[i-1];"
    << "\n  write: x[i];"
    << "\n  (future & silent)"
    << "\n    (1==1"
    ;
  oput_uniring_invariant(ofile, actset, domsz, "\n     && ", 0);
  ofile << "\n    );";
  ofile << "\n  puppet:";
  for each_in_BitTable(actid , actset) {
    UniAct act = act_of_id(actid, opt.domsz);
    ofile << "\n    "
      << "( x[i-1]==" << act[0]
      << " && x[i]==" << act[1]
      << " --> x[i]:=" << act[2] << "; )";
  }
  ofile << "\n    ;";
  ofile << "\n}\n";
}


static void
oput_graphviz(OFile& ofile, const BitTable& set, uint domsz)
{
  ofile << "digraph G {\n"
    << " margin=0;\n"
    << " edge [weight=5];\n\n";

  for (PcState a = 0; a < domsz; ++a) {
    ofile << "  s_" << a
      << " [label=\"" << a << "\"];\n";
  }

  for each_in_BitTable(actid , set) {
    UniAct act = act_of_id(actid, domsz);

    ofile << "  "
      << "s_" << act[0] << " -> " << "s_" << act[2]
      << "[label=\"" << act[1] << "\"];\n";
  }
  ofile << "}\n";
}

static bool
xget_BitTable (C::XFile* xfile, BitTable& set)
{
  C::XFile olay[1];
  if (!getlined_olay_XFile (olay, xfile, "\n"))
    return false;
  skipds_XFile (olay, 0);
  set.wipe(0);
  for (uint i = 0; i < set.sz(); ++i) {
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
      set.set1(i);
    }
  }
  return true;
}

static void
filter_stdin (const FilterOpt& opt, OFile& ofile)
{
  const uint domsz = opt.domsz;
  BitTable set( domsz*domsz*domsz, 0 );
  C::XFile* xfile = stdin_XFile ();
  while (xget_BitTable (xfile, set)) {
    if (opt.echo_bits) {
      ofile << set;

      if (opt.count_ones) {
        ofile << ' ' << set.count();
      }

      ofile << '\n';
    }

    if (opt.xlate_invariant) {
      oput_uniring_invariant (ofile, set, domsz, "", " && ");
      ofile << '\n';
    }
    if (opt.prot_ofilename) {
      oput_uniring_protocon_file("", opt.prot_ofilename, set, opt);
    }
    if (opt.graphviz_ofilename) {
      OFileB graphviz_ofileb;
      OFile graphviz_ofile( graphviz_ofileb.uopen(0, opt.graphviz_ofilename) );
      oput_graphviz(graphviz_ofile, set, domsz);
    }
  }
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
    else if (eq_cstr ("-max-depth", arg)) {
      if (!xget_uint_cstr (&opt.max_depth, argv[argi++]))
        failout_sysCx("Argument Usage: -max-depth n\nWhere n is an unsigned integer!");
    }
    else if (eq_cstr ("-minsz", arg)) {
      if (!xget_uint_cstr (&opt.minsz, argv[argi++]))
        failout_sysCx("Argument Usage: -minsz n\nWhere n is an unsigned integer!");
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
    else if (eq_cstr ("-o-graphviz", arg)) {
      filter = true;
      opt.graphviz_ofilename = argv[argi++];
      if (!opt.graphviz_ofilename)
        failout_sysCx("Argument Usage: -o-graphviz file");
    }
    else if (eq_cstr ("-o-prot", arg)) {
      filter = true;
      opt.prot_ofilename = argv[argi++];
      if (!opt.prot_ofilename)
        failout_sysCx("Argument Usage: -o-spec file");
    }
    else  {
      DBog1( "Unrecognized option: %s", arg );
      failout_sysCx (0);
    }
  }
  OFile ofile( stdout_OFile () );

  if (filter) {
    filter_stdin (opt, ofile);
  }
  else {
    searchit(opt, ofile);
  }
  lose_sysCx ();
  return 0;
}

END_NAMESPACE

int main(int argc, char** argv) {
  return PROJECT_NAMESPACE::main(argc, argv);
}
