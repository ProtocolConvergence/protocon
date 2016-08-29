
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
#include "../pfmla.hh"

#include "../namespace.hh"

#define each_in_BitTable(i , bt) \
  (zuint i = bt.begidx(); i < bt.sz(); bt.nextidx(&i))

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
  uint max_period;
  uint max_propagations;
  bool check_ppg_overapprox;
  bool self_disabling_tiles;
  bool count_ones;
  bool verify;
  bool use_bdds;
  const char* record_sep;
  const char* prot_ofilename;
  const char* graphviz_ofilename;
  const char* svg_livelock_ofilename;
  const char* list_ofilename;

  PFmlaCtx pfmla_ctx;
  Table<PFmlaVbl> pfmla_vbls;
  uint allbut2_pfmla_list_id;

  FilterOpt()
    : domsz( 3 )
    , max_depth( 0 )
    , max_period( 0 )
    , max_propagations( 0 )
    , check_ppg_overapprox( true )
    , self_disabling_tiles( false )
    , count_ones( false )
    , verify( false )
    , use_bdds( false )
    , record_sep( 0 )
    , prot_ofilename( 0 )
    , graphviz_ofilename( 0 )
    , svg_livelock_ofilename( 0 )
    , list_ofilename( 0 )
  {}

  void commit_domsz() {
    if (max_depth == 0)
      max_depth = domsz*domsz;
    if (max_period == 0)
      max_period = 2*domsz+2;
    if (max_propagations == 0)
      max_propagations = domsz*domsz;

    if (use_bdds) {
      pfmla_vbls.affysz(1+max_period);
      for (uint i = 0; i < 1+max_period; ++i) {
        uint vbl_id = pfmla_ctx.add_vbl((String("x") << i), domsz);
        pfmla_vbls[i] = pfmla_ctx.vbl(vbl_id);
      }
      allbut2_pfmla_list_id = pfmla_ctx.add_vbl_list();
      for (uint i = 0; i+2 < 1+max_period; ++i) {
        pfmla_ctx.add_to_vbl_list(allbut2_pfmla_list_id,
                                  id_of(pfmla_vbls[i]));
      }
    }
  }
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

  void
permute_pc_act (BitTable& bt, const BitTable& set, const Table<uint>& perm_map)
{
  const uint domsz = perm_map.sz();
  bt.wipe(0);
  for each_in_BitTable(actid , set) {
    UniAct act = UniAct::of_id(actid, domsz);
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

static
  void
init_ppgfun(Table<PcState>& ppgfun, const BitTable& delegates, const uint domsz)
{
  ppgfun.affysz(domsz*domsz, domsz);
  for each_in_BitTable(actid , delegates) {
    UniAct act = UniAct::of_id(actid, domsz);
    ppgfun[id_of2(act[0], act[1], domsz)] = act[2];
  }
}

  void
map_livelock_ppgs(void (*f) (void**, const UniAct&, uint, uint),
                  void** ctx,
                  const Table<PcState>& bot,
                  const Table<PcState>& col,
                  const Table<PcState>& ppgfun,
                  const uint domsz)
{
  const uint n = bot.sz() - 1;
  const uint m = col.sz() - 1;
  Claim( bot[0] == bot[n] );
  Claim( bot[0] == col[m] );
  Claim( bot[0] == col[0] );
  Table<PcState> row;
  row.affysz(n+1);
  for (uint j = 1; j < n+1; ++j) {
    row[j] = bot[j];
  }
  for (uint i = 1; i < m+1; ++i) {
    row[0] = col[i];
    for (uint j = 1; j < n+1; ++j) {
      const PcState a = row[j-1];
      const PcState b = row[j];
      const PcState c = ppgfun[id_of2(a, b, domsz)];
      Claim( c < domsz );
      row[j] = c;
      f(ctx, UniAct(a, b, c), i-1, j-1);
    }
  }
}

bool fill_livelock_ck(const Table<PcState>& top,
                      const Table<PcState>& col,
                      const uint top_rowidx,
                      const Table<PcState>& ppgfun,
                      const uint domsz,
                      Table<PcState>& row)
{
  const uint n = top.sz() - 1;
  Claim( top[0] == top[n] );
  Claim( top[0] == col[col.sz()-1] );
  Claim( top[0] == col[top_rowidx] );
  row.ensize(n+1);
  for (uint j = 0; j < n+1; ++j) {
    row[j] = top[j];
  }
  for (uint i = top_rowidx+1; i < col.sz(); ++i) {
    row[0] = col[i];
    for (uint j = 1; j < n+1; ++j) {
      row[j] = ppgfun[id_of2(row[j-1], row[j], domsz)];
      if (row[j] == domsz)  return false;
    }
    if (row[0] != row[n])  return false;
  }
  for (uint j = 0; j < n+1; ++j) {
    if (row[j] != top[j])  return false;
  }
  return true;
}

  Trit
livelock_semick_rec(const Table<PcState>& old_bot,
                    const Table<PcState>& old_col,
                    uint limit,
                    const Table<PcState>& ppgfun,
                    const uint domsz,
                    Table<PcState>& ret_row,
                    Table<PcState>& ret_col)
{
  const uint n = old_bot.sz();
  Table<PcState> bot, col;
  bot.affysz(n+1);  col.affysz(n+1);
  for (uint i = 0; i < n; ++i) {
    bot[i] = old_bot[i];
  }
  bool may_exist = false;
  // Build the diagonal up and to the right.
  for (PcState diag_val = 0; diag_val < domsz; ++diag_val) {
    col[0] = diag_val;
    bool col_exists = true;
    for (uint i = 1; i < n+1; ++i) {
      col[i] = ppgfun[id_of2(old_col[i-1], col[i-1], domsz)];
      if (col[i] == domsz) {
        col_exists = false;
        break;
      }
    }
    skip_unless (col_exists);
    bot[n] = col[n];
    if (bot[0]==bot[n]) {
      for (uint i = n; i-- > 0;) {
        skip_unless (col[i] == col[n]);
        if (fill_livelock_ck(bot, col, i, ppgfun, domsz, ret_row)) {
          ret_col.ensize(n+1-i);
          for (uint j = 0; j < ret_col.sz(); ++j) {
            ret_col[j] = col[i+j];
          }
          return Yes;
        }
      }
    }
    if (n == limit) {
      may_exist = true;
      continue;
    }
    Trit found =
      livelock_semick_rec(bot, col, limit, ppgfun,
                          domsz, ret_row, ret_col);
    if (found == Yes)  return Yes;
    may_exist = (may_exist || (found == May));
  }
  return (may_exist ? May : Nil);
}

  Trit
livelock_semick(const uint limit,
                const Table<PcState>& ppgfun,
                const uint domsz,
                Table<PcState>* ret_row=0,
                Table<PcState>* ret_col=0)
{
  Table<PcState> bot, col, tmp_row, tmp_col;
  bot.affysz(1);  col.affysz(1);
  bool may_exist = false;
  for (uint c = 0; c < domsz; ++c) {
    bot[0] = col[0] = c;
    Trit found = livelock_semick_rec(bot, col, limit, ppgfun,
                                     domsz, tmp_row, tmp_col);
    if (found == Yes) {
      if (ret_row)  *ret_row = tmp_row;
      if (ret_col)  *ret_col = tmp_col;
      return Yes;
    }
    may_exist = (may_exist || (found == May));
  }
  return (may_exist ? May : Nil);
}

  Trit
guided_livelock_semick_rec(const Table<uint>& top_row,
                           uint mid_west,
                           const Table< Tuple<uint,2> >& match_row,
                           uint limit,
                           const Table<PcState>& ppgfun,
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
      guided_livelock_semick_rec(mid_row, bot_west,
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
guided_livelock_ck(const Table< Tuple<uint,2> >& acts,
                   const Table<PcState>& ppgfun,
                   const uint domsz,
                   BitTable& livelockset,
                   const uint limit)
{
  livelockset.wipe(0);
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
      guided_livelock_semick_rec(top_row, mid_west,
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

  void
fill_livelock_actions_fn(void** data, const UniAct& act, uint rowidx, uint colidx) {
  (void) rowidx;
  (void) colidx;
  ((BitTable*) data[0])->set1(id_of(act, *(PcState*) data[1]));
}

/** Given a list of actions and variables x[j-1] and x[j],
 * compute the tiling constraints for column j
 * in the form of a transition formula.
 **/
static
  X::Fmla
column_xfmla(const BitTable& actset, const PFmlaVbl& x_p, const PFmlaVbl& x_j, uint domsz)
{
  X::Fmla xn( false );
  for each_in_BitTable( actid, actset ) {
    const UniAct act = UniAct::of_id(actid, domsz);
    //    x'[j-1]==a         && x[j]==b     && x'[j]==c
    xn |= x_p.img_eq(act[0]) && x_j==act[1] && x_j.img_eq(act[2]);
  }
  return xn;
}

  Trit
periodic_leads_semick(const BitTable& delegates,
                      BitTable& mask,
                      Table<BitTable>& candidates_stack,
                      const uint depth,
                      const FilterOpt& opt)
{
  const uint domsz = opt.domsz;
  BitTable& candidates = candidates_stack[depth];

  if (opt.use_bdds) {
    bool livelock_found = false;
    X::Fmla lo_xn(true);
    X::Fmla hi_xn(true);
    X::Fmla lo_col_xn;
    X::Fmla hi_col_xn;
    const Table<PFmlaVbl>& vbls = opt.pfmla_vbls;
    Claim( vbls.sz() == 1+opt.max_period );
    for (uint j = 1; j < 1+opt.max_period; ++j) {
      lo_col_xn =
        column_xfmla(delegates, vbls[j-1], vbls[j], domsz);
      lo_xn &= lo_col_xn;

      if (opt.check_ppg_overapprox) {
        hi_col_xn = lo_col_xn |
          column_xfmla(candidates, vbls[j-1], vbls[j], domsz);
        hi_xn &= hi_col_xn;
      }

      const X::Fmla periodic_xn = lo_xn &
        (vbls[0]==vbls[j]) & vbls[0].img_eq_img(vbls[j]);

      if (periodic_xn.cycle_ck(0)) {
        livelock_found = true;
        break;
      }
    }
    if (livelock_found)
      return Nil;

    P::Fmla scc(false);
    if (lo_xn.cycle_ck(&scc)) {
      X::Fmla last_tile = (scc & lo_xn);
      last_tile = last_tile.smooth(opt.allbut2_pfmla_list_id);
      last_tile = last_tile.smooth_pre(opt.pfmla_vbls[opt.max_period-1]);
      if (lo_col_xn.equiv_ck(last_tile)) {
        return Yes;
      }
    }

    if (!opt.check_ppg_overapprox) {
      return May;
    }

    if (!hi_xn.cycle_ck(&scc)) {
      return Nil;
    }
    else {
      X::Fmla last_tile = (scc & hi_xn);
      last_tile = last_tile.smooth(opt.allbut2_pfmla_list_id);
      last_tile = last_tile.smooth_pre(opt.pfmla_vbls[opt.max_period-1]);
      if (!lo_col_xn.subseteq_ck(last_tile)) {
        return Nil;
      }
    }
    return May;
  }

  Table<PcState> ppgfun;
  init_ppgfun(ppgfun, delegates, domsz);
  const bool detect_livelocks_well = true;

  bool maybe_livelock = true;
  if (detect_livelocks_well) {
    Table<PcState> live_row, live_col;
    Trit livelock_found =
      livelock_semick(opt.max_period, ppgfun, domsz, &live_row, &live_col);
    if (livelock_found == Nil) {
      maybe_livelock = false;
    }
    else if (livelock_found == Yes) {
      {
        PcState tmp_domsz = domsz;
        mask.wipe(0);
        void* data[2] = { &mask, &tmp_domsz };
        map_livelock_ppgs(fill_livelock_actions_fn, data, live_row, live_col,
                          ppgfun, domsz);
      }
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
      const UniAct mid_act = UniAct::of_id(actid, domsz);
      const PcState a = mid_act[0], b = mid_act[1], c = mid_act[2];

      for (PcState d = 0; d < domsz; ++d) {
        const UniAct bot_mask_act(domsz, c, d);
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

  mask = delegates;
  mask |= candidates;

  AdjList<uint> overapprox_digraph( digraph.nnodes() );
  DoTwice(overapprox_digraph.commit_degrees()) {
    skip_unless (opt.check_ppg_overapprox);
    for each_in_BitTable(actid , mask) {
      const UniAct mid_act = UniAct::of_id(actid, domsz);
      const PcState a = mid_act[0], b = mid_act[1], c = mid_act[2];

      for (PcState d = 0; d < domsz; ++d) {
        const UniAct bot_mask_act(domsz, c, d);
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

  for each_in_BitTable(actid , pending) {
    const UniAct act = UniAct::of_id(actid, domsz);
    bool found = false;
    // Find all starting nodes.
    for (PcState d = 0; d < domsz; ++d) {
      const uint node_id = id_of3(act[0], act[1], d, domsz);
      skip_unless (cycle_ck_from(node_id, digraph, stack, mask));
      found = true;
      break;
    }

    if (!found) {
      maybe_livelock = false;
      if (opt.check_ppg_overapprox) {
        for (PcState d = 0; d < domsz; ++d) {
          const uint node_id = id_of3(act[0], act[1], d, domsz);
          skip_unless (cycle_ck_from(node_id, overapprox_digraph, stack, mask));
          found = true;
          break;
        }
        if (!found) {
          return Nil;
        }
      }
      continue;
    }

    for (uint i = 0; i < stack.sz(); ++i) {
      Triple<uint> node = UniAct::of_id(stack[i][0], domsz);
      const PcState a = node[0];
      const PcState b = node[1];
      const PcState c = ppgfun[id_of2(a, b, domsz)];
      Claim( c < domsz );
      pending.set0(id_of3(a, b, c, domsz));

      // Change this stack to more easily represent the livelock.
      stack[i][0] = a;
      stack[i][1] = b;
    }
    if (stack.sz() <= opt.max_period &&
        guided_livelock_ck(stack, ppgfun, domsz, mask,
                           opt.max_propagations)) {
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

  return (maybe_livelock ? Yes : May);
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
trim_coexist (BitTable& actset, uint actid, uint domsz,
              bool self_disabling_tiles)
{
  UniAct act( UniAct::of_id(actid, domsz) );

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

  if (!self_disabling_tiles)  return;
  // Enforce N-disabling.
  subtract_action_mask(actset, UniAct(act[2], act[1], domsz), domsz);
  subtract_action_mask(actset, UniAct(domsz, act[1], act[0]), domsz);
}

  void
recurse(Table<BitTable>& delegates_stack,
        Table<BitTable>& candidates_stack,
        uint actid,
        const FilterOpt& opt, OFile& ofile,
        uint depth,
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
  trim_coexist(candidates, actid, domsz, opt.self_disabling_tiles);

  bool print_delegates = true;
  switch (periodic_leads_semick(delegates, mask,
                                candidates_stack, depth, opt)) {
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
  if (depth == opt.max_depth)
    return;

  for (uint next_actid = actid+1; next_actid < candidates.sz(); ++next_actid) {
    skip_unless (candidates.ck(next_actid));
    recurse(delegates_stack, candidates_stack,
            next_actid, opt, ofile, depth+1, mask);

    // This must be after recurse() so that the livelock
    // detection doesn't remove valid candidates.
    candidates.set0(next_actid);
  }
}

  void
searchit(const FilterOpt& opt, OFile& ofile)
{
  const uint domsz = opt.domsz;
  const uint max_depth = opt.max_depth;

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
  recurse(delegates_stack, candidates_stack, actid, opt, ofile, 1, mask)

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
    UniAct act = UniAct::of_id(actid, domsz);
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
    UniAct act = UniAct::of_id(actid, domsz);
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
    UniAct act = UniAct::of_id(actid, domsz);

    ofile << "  "
      << "s_" << act[0] << " -> " << "s_" << act[2]
      << "[label=\"" << act[1] << "\"];\n";
  }
  ofile << "}\n";
}

static void
oput_svg_tile(OFile& ofile, const UniAct& act, uint y, uint x, uint d)
{
  const char rect_style[] = " fill=\"none\" stroke=\"black\" stroke-width=\"4\"";
  const char line_style[] = " stroke=\"black\" stroke-width=\"2\"";
  const char text_style[] = " fill=\"black\" font-family=\"Latin Modern, sans\" text-anchor=\"middle\"";
  //" dominant-baseline=\"middle\"";
  const char text_nw_style[] = " font-size=\"24\"";
  const char text_se_style[] = " font-size=\"32\"";
#define LOC(x,p)  (x+p*d/100)
  ofile
    << "\n<rect x=\"" << x << "\" y=\"" << y
    << "\" width=\"" << d << "\" height=\"" << d << "\"" << rect_style << " />"
    << "\n<line x1=\"" << x << "\" y1=\"" << (y+d)
    << "\" x2=\"" << LOC(x,100) << "\" y2=\"" << y << "\"" << line_style << " />"
    << "<line x1=\"" << x << "\" y1=\"" << y
    << "\" x2=\"" << LOC(x,50) << "\" y2=\"" << LOC(y,50) << "\"" << line_style << " />"
    << "\n<text x=\"" << LOC(x,20) << "\" y=\"" << LOC(y,57) << "\""
    << text_style << text_nw_style << ">" << act[0] << "</text>"
    << "\n<text x=\"" << LOC(x,50) << "\" y=\"" << LOC(y,27) << "\""
    << text_style << text_nw_style << ">" << act[1] << "</text>"
    << "\n<text x=\"" << LOC(x,70) << "\" y=\"" << LOC(y,85) << "\""
    << text_style << text_se_style << ">" << act[2] << "</text>"
    ;
#undef LOC
}

static void
oput_svg_tile_callback(void** data, const UniAct& act, uint i, uint j)
{
  const uint d = *(uint*)data[1];
  const uint border = *(uint*)data[2];
  oput_svg_tile(*(OFile*)data[0], act, i*d+border, j*d+border, d);
}


static void
oput_svg_livelock(OFile& ofile, const Table<PcState>& ppgfun,
                  const Table<PcState>& bot,
                  const Table<PcState>& col,
                  const PcState domsz)
{
  const uint n = bot.sz()-1;
  const uint m = col.sz()-1;
  const uint d = 100;
  const uint border = 3;
  ofile << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
    << "\n<!DOCTYPE svg PUBLIC \"-//W3C//DTD SVG 1.1 Basic//EN\""
    << " \"http://www.w3.org/Graphics/SVG/1.1/DTD/svg11-basic.dtd\">"
    << "\n<svg xmlns=\"http://www.w3.org/2000/svg\" xmlns:xlink=\"http://www.w3.org/1999/xlink\""
    << " version=\"1.1\" baseProfile=\"basic\" id=\"svg-root\""
    << " width=\"" << (n*d + 2*border) << "\" height=\"" << (m*d + 2*border) << "\">"
    << "\n<rect x=\"0\" y=\"0\""
    << " width=\""  << (n*d + 2*border) << "\""
    << " height=\"" << (m*d + 2*border) << "\""
    << " fill=\"white\" stroke=\"white\" stroke-width=\"0\" />"
    ;

  {
    uint tmp_d = d;
    uint tmp_border = border;
    void* data[3] = { &ofile, &tmp_d, &tmp_border };
    map_livelock_ppgs(oput_svg_tile_callback, data,
                      bot, col, ppgfun, domsz);
  }

  ofile << "\n</svg>";
}

static bool
xget_BitTable (C::XFile* xfile, BitTable& set)
{
  C::XFile olay[1];
  if (!getlined_olay_XFile (olay, xfile, "\n"))
    return false;
  skipds_XFile (olay, 0);
  set.wipe(0);
  char c;
  for (uint i = 0; i < set.sz(); ++i) {
    if (xget_char_XFile (olay, &c)) {
      if (c != '0' && c != '1') {
        failout_sysCx ("unknown char!");
      }
      if (c == '1')
        set.set1(i);
    }
    else if (i == 0) {
      return false;
    }
    else {
      failout_sysCx ("not enough bits!");
    }
  }
  // TODO: This read call should just fail, not return the NUL character.
  if (xget_char_XFile (olay, &c) && c != '\0') {
    failout_sysCx ("too many bits!");
  }
  return true;
}

static void
filter_stdin (const FilterOpt& opt, OFile& ofile)
{
  const uint domsz = opt.domsz;
  BitTable actset( domsz*domsz*domsz, 0 );
  C::XFile* xfile = stdin_XFile ();
  const char* record_sep = 0;
  while (xget_BitTable (xfile, actset)) {
    if (opt.count_ones) {
      ofile << ' ' << actset.count() << '\n';
    }
    if (record_sep)
      ofile << record_sep << '\n';
    else
      record_sep = opt.record_sep;

    if (opt.verify || opt.svg_livelock_ofilename) {
      Table<PcState> ppgfun, top, col;
      init_ppgfun(ppgfun, actset, domsz);
      Trit livelock_exists =
        livelock_semick(opt.max_period, ppgfun, domsz, &top, &col);

      if (opt.verify) {
        switch (livelock_exists) {
          case Nil: ofile << "silent\n";  break;
          case May: ofile << "unknown\n";  break;
          case Yes: ofile << "livelock\n";  break;
        }
      }

      if (opt.svg_livelock_ofilename) {
        OFileB svg_ofileb;
        OFile svg_ofile( svg_ofileb.uopen(0, opt.svg_livelock_ofilename) );
        oput_svg_livelock(svg_ofile, ppgfun, top, col, domsz);
      }
    }

    if (opt.prot_ofilename) {
      oput_uniring_protocon_file("", opt.prot_ofilename, actset, opt);
    }

    if (opt.graphviz_ofilename) {
      OFileB graphviz_ofileb;
      OFile graphviz_ofile( graphviz_ofileb.uopen(0, opt.graphviz_ofilename) );
      oput_graphviz(graphviz_ofile, actset, domsz);
    }

    if (opt.list_ofilename) {
      OFileB list_ofileb;
      OFile list_ofile( list_ofileb.uopen(0, opt.list_ofilename) );
      for each_in_BitTable( actid, actset ) {
        const UniAct act = UniAct::of_id(actid, domsz);
        list_ofile << act[0] << '\t' << act[1] << '\t' << act[2] << '\n';
      }
    }
  }
}

static bool TestKnownAperiodic();

int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);
  bool filter = false;
  FilterOpt opt;

  while (argi < argc) {
    const char* arg = argv[argi++];
    if (eq_cstr ("-domsz", arg)) {
      if (!xget_uint_cstr (&opt.domsz, argv[argi++]))
        failout_sysCx("Argument Usage: -domsz <M>\nWhere <M> is an unsigned integer!");
    }
    else if (eq_cstr ("-max-depth", arg)) {
      if (!xget_uint_cstr (&opt.max_depth, argv[argi++]))
        failout_sysCx("Argument Usage: -max-depth <limit>\nWhere <limit> is an unsigned integer!");
    }
    else if (eq_cstr ("-max-period", arg)) {
      if (!xget_uint_cstr (&opt.max_period, argv[argi++]))
        failout_sysCx("Argument Usage: -max-period <limit>\nWhere <limit> is an unsigned integer!");
    }
    else if (eq_cstr ("-max-ppgs", arg) ||
             eq_cstr ("-max-propagations", arg)) {
      if (!xget_uint_cstr (&opt.max_propagations, argv[argi++]))
        failout_sysCx("Argument Usage: -max-ppgs <limit>\nWhere <limit> is an unsigned integer!");
    }
    else if (eq_cstr ("-self-disabling-tiles", arg)) {
      opt.self_disabling_tiles = true;
    }
    else if (eq_cstr ("-test", arg)) {
      bool passed = TestKnownAperiodic();
      if (passed) {
        DBog0("PASS");
      }
      else {
        DBog0("FAIL");
      }
      lose_sysCx();
      return (passed ? 0 : 1);
    }
    else if (eq_cstr ("-count-ones", arg)) {
      filter = true;
      opt.count_ones = true;
    }
    else if (eq_cstr ("-verify", arg)) {
      filter = true;
      opt.verify = true;
    }
    else if (eq_cstr ("-o-graphviz", arg)) {
      filter = true;
      opt.graphviz_ofilename = argv[argi++];
      if (!opt.graphviz_ofilename)
        failout_sysCx("Argument Usage: -o-graphviz <file>");
    }
    else if (eq_cstr ("-o-prot", arg)) {
      filter = true;
      opt.prot_ofilename = argv[argi++];
      if (!opt.prot_ofilename)
        failout_sysCx("Argument Usage: -o-prot <file>");
    }
    else if (eq_cstr ("-o-svg-livelock", arg) ||
             eq_cstr ("-o-svg", arg)) {
      filter = true;
      opt.svg_livelock_ofilename = argv[argi++];
      if (!opt.svg_livelock_ofilename)
        failout_sysCx("Argument Usage: -o-svg-livelock <file>");
    }
    else if (eq_cstr ("-o-list", arg)) {
      filter = true;
      opt.list_ofilename = argv[argi++];
      if (!opt.list_ofilename)
        failout_sysCx("Argument Usage: -o-list <file>");
    }
    else if (eq_cstr ("-RS", arg)) {
      filter = true;
      opt.record_sep = argv[argi++];
      if (!opt.record_sep)
        failout_sysCx("Argument Usage: -RS <separator>");
    }
    else  {
      DBog1( "Unrecognized option: %s", arg );
      failout_sysCx (0);
    }
  }
  OFile ofile( stdout_OFile () );

  opt.commit_domsz();

  if (filter) {
    filter_stdin (opt, ofile);
  }
  else {
    searchit(opt, ofile);
  }
  lose_sysCx ();
  return 0;
}

  bool
TestKnownAperiodic()
{
  const uint domsz = 29;
  static const uint AperiodicTileset[][3] = {
    {  0, 13,  8 }, {  0, 14, 10 }, {  0, 15, 12 }, {  0, 16, 12 },
    {  0, 17,  9 }, {  0, 18,  8 }, {  0, 19, 10 }, {  0, 20, 10 },
    {  0, 21, 10 }, {  0, 22,  7 }, {  0, 23, 11 }, {  0, 24, 11 },
    {  0, 25,  7 }, {  0, 26,  7 }, {  0, 27,  9 }, {  0, 28,  9 },
    {  1,  7, 13 }, {  1, 11, 14 },
    {  2,  9, 15 }, {  2, 10, 16 }, {  2, 11, 17 },
    {  3,  8, 18 }, {  3,  9, 19 }, {  3, 10, 20 }, {  3, 12, 21 },
    {  4,  8, 22 }, {  4,  9, 23 }, {  4, 10, 24 },
    {  5,  7, 25 }, {  5,  8, 26 },
    {  6,  9, 27 }, {  6, 12, 28 },
    {  7,  3,  0 }, {  7,  4,  0 }, {  7,  6,  0 },
    {  8,  2,  0 }, {  8,  6,  0 },
    {  9,  1,  0 }, {  9,  3,  0 }, {  9,  4,  0 },
    { 10,  1,  0 }, { 10,  3,  0 }, { 10,  4,  0 }, { 10,  5,  0 },
    { 11,  4,  0 }, { 11,  5,  0 },
    { 12,  1,  0 }, { 12,  2,  0 },
    { 13,  0,  2 },
    { 14,  0,  1 },
    { 15,  0,  2 },
    { 16,  0,  1 },
    { 17,  0,  1 },
    { 18,  0,  6 },
    { 19,  0,  4 },
    { 20,  0,  5 },
    { 21,  0,  3 },
    { 22,  0,  6 },
    { 23,  0,  4 },
    { 24,  0,  5 },
    { 25,  0,  4 },
    { 26,  0,  3 },
    { 27,  0,  4 },
    { 28,  0,  3 }
  };
  const uint depth = ArraySz(AperiodicTileset);

  BitTable delegates( domsz*domsz*domsz, 0 );
  for (uint i = 0; i < ArraySz(AperiodicTileset); ++i) {
    const uint* tile = AperiodicTileset[i];
    delegates.set1(id_of3(tile[0], tile[1], tile[2], domsz));
  }

  Table<PcState> ppgfun;
  init_ppgfun(ppgfun, delegates, domsz);

  switch (livelock_semick(15, ppgfun, domsz)) {
    case Nil: DBog0("livelock: Nil");  return false;
    case May: break;
    case Yes: DBog0("livelock: Yes");  return false;
  }

  BitTable mask( domsz*domsz*domsz, 0 );
  Table<BitTable> candidates_stack(depth+1, mask);
  FilterOpt opt;
  opt.domsz = domsz;
  opt.max_period = 10;
  opt.check_ppg_overapprox = false;
  opt.commit_domsz();
  switch (periodic_leads_semick(delegates, mask,
                                candidates_stack, depth, opt)) {
    case Nil: DBog0("hard: Nil");  return false;
    case May: DBog0("hard: May");  return false;
    case Yes: break;
  }
  return true;
}


END_NAMESPACE

int main(int argc, char** argv) {
  return PROJECT_NAMESPACE::main(argc, argv);
}
