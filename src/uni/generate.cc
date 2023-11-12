
#include <algorithm>

#include <fildesh/istream.hh>
#include <fildesh/ostream.hh>

#include "adjlist.hh"
#include "canonical.hh"
#include "livelock.hh"
#include "uniact.hh"
#include "unifile.hh"

#include "src/pfmla.hh"

#include "src/cx/bittable.hh"
#include "src/cx/table.hh"

extern "C" {
#include "src/cx/syscx.h"
}
#include "src/namespace.hh"

struct SearchOpt
{
  uint domsz;
  uint max_depth;
  uint max_period;
  uint max_propagations;
  bool check_ppg_overapprox;
  bool nw_deterministic;
  bool nw_commutative;
  bool nw_disabling;
  bool nn_ww_disabling;
  bool use_bdds;
  bool line_flush;
  bool trust_given;

  std::ostream* id_ofile;
  std::ostream* bfs_ofile;

  uint dfs_threshold;

  PFmlaCtx pfmla_ctx;
  Table<PFmlaVbl> pfmla_vbls;
  uint allbut2_pfmla_list_id;

  Table<UniAct> given_acts;

  SearchOpt()
    : domsz( 0 )
    , max_depth( 0 )
    , max_period( 0 )
    , max_propagations( 0 )
    , check_ppg_overapprox( true )
    , nw_deterministic( true )
    , nw_commutative( false )
    , nw_disabling( false )
    , nn_ww_disabling( false )
    , use_bdds( false )
    , line_flush( true )
    , trust_given( false )
    , id_ofile( &std::cout )
    , bfs_ofile( NULL )
    , dfs_threshold( 0 )
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
init_ppgfun(Table<PcState>& ppgfun, const BitTable& delegates, const uint domsz)
{
  ppgfun.affysz(domsz*domsz, domsz);
  for each_in_BitTable(actid , delegates) {
    UniAct act = UniAct::of_id(actid, domsz);
    ppgfun[id_of2(act[0], act[1], domsz)] = act[2];
  }
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

static
  unsigned
commute_action_id(unsigned id, unsigned domsz)
{
  UniAct act = UniAct::of_id(id, domsz);
  return id_of3(act[1], act[0], act[2], domsz);
}

  Trit
periodic_leads_semick(const BitTable& delegates,
                      const Table<PcState>& ppgfun,
                      BitTable& mask,
                      Table<BitTable>& candidates_stack,
                      const uint depth,
                      const SearchOpt& opt)
{
#define PruneLivelocks
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
#ifdef PruneLivelocks
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
          if (opt.nw_commutative) {
            candidates_stack[i].set0(
                commute_action_id(max_livelock_actids[1], domsz));
          }
        }
      }
#endif
      return Nil;
    }
  }

  AdjList<uint> digraph( domsz*domsz*domsz );
  make_tile_cont_digraph(digraph, delegates, ppgfun, domsz);

  AdjList<uint> overapprox_digraph( digraph.nnodes() );
  if (opt.check_ppg_overapprox) {
    mask = delegates;
    mask |= candidates;
    make_overapprox_tile_cont_digraph(overapprox_digraph, mask, domsz);
  }
  else {
    overapprox_digraph.commit_degrees();
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
      Triple<PcState> node = UniAct::of_id(stack[i][0], domsz);
      const PcState a = node[0];
      const PcState b = node[1];
      const PcState c = ppgfun[id_of2(a, b, domsz)];
      Claim( c < domsz );
      pending.set0(id_of3(a, b, c, domsz));

      // Change this stack to more easily represent the livelock.
      stack[i][0] = a;
      stack[i][1] = b;
    }
    if (opt.max_propagations > opt.max_period &&
        stack.sz() <= opt.max_period &&
        guided_livelock_ck(stack, ppgfun, domsz, mask,
                           opt.max_propagations)) {
#ifdef PruneLivelocks
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
#undef PruneLivelocks
#endif
      return Nil;
    }
  }

  return (maybe_livelock ? Yes : May);
}


#define TRIM_MASK(a, b, c) \
  subtract_action_mask(candidates, UniAct(a,b,c), domsz, delegates)

static
  void
abc_checkem(unsigned a, unsigned b, unsigned c, unsigned domsz,
            const BitTable& delegates, BitTable& candidates)
{
  // a,b,c => c,x,y => no a,y,z && no b,y,z
  for (unsigned x = 0; x < domsz; ++x) {
    for (unsigned y = 0; y < domsz; ++y) {
      unsigned cxy_id = id_of(UniAct(c, x, y), domsz);
      if (delegates.ck(cxy_id)) {
        TRIM_MASK(a, y, domsz);
        TRIM_MASK(y, a, domsz);
        TRIM_MASK(b, y, domsz);
        TRIM_MASK(y, b, domsz);
      }
    }
  }
  // a,b,c => a,y,z => no c,x,y
  for (unsigned y = 0; y < domsz; ++y) {
    for (unsigned z = 0; z < domsz; ++z) {
      unsigned ayz_id = id_of(UniAct(a, y, z), domsz);
      unsigned byz_id = id_of(UniAct(b, y, z), domsz);
      if (delegates.ck(ayz_id) || delegates.ck(byz_id)) {
        TRIM_MASK(c, domsz, y);
        TRIM_MASK(domsz, c, y);
      }
    }
  }
}

static
  void
cxy_checkem(unsigned c, unsigned x, unsigned y, unsigned domsz,
            const BitTable& delegates, BitTable& candidates)
{
  // c,x,y => a,b,c => no a,y,z && no b,y,z
  for (unsigned a = 0; a < domsz; ++a) {
    for (unsigned b = 0; b < domsz; ++b) {
      unsigned abc_id = id_of(UniAct(a, b, c), domsz);
      unsigned abx_id = id_of(UniAct(a, b, x), domsz);
      if (delegates.ck(abc_id) || delegates.ck(abx_id)) {
        TRIM_MASK(a, y, domsz);
        TRIM_MASK(y, a, domsz);
        TRIM_MASK(b, y, domsz);
        TRIM_MASK(y, b, domsz);
      }
    }
  }
  // c,x,y => a,y,z => no a,b,c
  // c,x,y => b,y,z => no a,b,c
  for (unsigned a = 0; a < domsz; ++a) {
    for (unsigned z = 0; z < domsz; ++z) {
      unsigned ayz_id = id_of(UniAct(a, y, z), domsz);
      if (delegates.ck(ayz_id)) {
        TRIM_MASK(a, domsz, c);
        TRIM_MASK(domsz, a, c);
        TRIM_MASK(a, domsz, x);
        TRIM_MASK(domsz, a, x);
      }
    }
  }
}

static
  void
ay_checkem(unsigned a, unsigned y, unsigned domsz,
           const BitTable& delegates, BitTable& candidates)
{
  // a,y,z => a,b,c => no c,x,y
  for (unsigned b = 0; b < domsz; ++b) {
    for (unsigned c = 0; c < domsz; ++c) {
      unsigned abc_id = id_of(UniAct(a, b, c), domsz);
      if (delegates.ck(abc_id)) {
        TRIM_MASK(c, domsz, y);
        TRIM_MASK(domsz, c, y);
      }
    }
  }
  // a,y,z => c,x,y => no a,b,c
  for (unsigned c = 0; c < domsz; ++c) {
    for (unsigned x = 0; x < domsz; ++x) {
      unsigned cxy_id = id_of(UniAct(c, x, y), domsz);
      if (delegates.ck(cxy_id)) {
        TRIM_MASK(a, domsz, c);
        TRIM_MASK(domsz, a, c);
      }
    }
  }
}

static
  void
trim_coexist(BitTable& candidates, unsigned actid,
             const SearchOpt& opt, const BitTable& delegates)
{
  const unsigned domsz = opt.domsz;
  UniAct act( UniAct::of_id(actid, domsz) );
  const bool nw_deterministic = opt.nw_deterministic;
  const bool nw_commutative = opt.nw_commutative;
  const bool nw_disabling = opt.nw_disabling;
  const bool nn_ww_disabling = opt.nn_ww_disabling;

  // The action itself.
  assert(candidates.ck(actid));
  if (nw_commutative) {
    const unsigned dual_id = id_of(UniAct(act[1], act[0], act[2]), domsz);
    assert(candidates.ck(dual_id));
  }

  // Trivial livelock.
  if (act[0]==act[1]) {
    TRIM_MASK(act[2], act[2], act[0]);
    if (nw_commutative) {
      TRIM_MASK(act[2], act[2], act[1]);
    }
  }

  // Trivial livelock.
  if (!nw_commutative && act[0]==act[2]) {
    TRIM_MASK(act[1], act[0], act[1]);
  }

  assert(nw_deterministic);
  // Enforce determinism.
  if (nw_deterministic) {
    for (unsigned c = 0; c < domsz; ++c) {
      if (c == act[2]) {continue;}
      TRIM_MASK(act[0], act[1], c);
      if (nw_commutative) {
        TRIM_MASK(act[1], act[0], c);
      }
    }
  }
  candidates.set0(id_of3(act[0], act[1], act[2], domsz));
  if (nw_commutative) {
    candidates.set0(id_of3(act[1], act[0], act[2], domsz));
  }

  // Enforce W-disabling.
  TRIM_MASK(act[0], act[2], domsz);
  TRIM_MASK(act[0], domsz, act[1]);

  if (nw_commutative) {
    TRIM_MASK(act[1], act[2], domsz);
    TRIM_MASK(act[1], domsz, act[0]);

    TRIM_MASK(act[2], act[0], domsz);
    TRIM_MASK(domsz, act[0], act[1]);
    assert(nw_disabling);
  }

  if (nw_disabling) {
    // Enforce N-disabling.
    TRIM_MASK(act[2], act[1], domsz);
    TRIM_MASK(domsz, act[1], act[0]);
  }

  if (nn_ww_disabling) {
    // a,b,c && c,x,y =>
    //   no a,y,z
    //   no b,y,z
    assert(nw_commutative);
    // a,b,c => c,x,y => no a,y,z && no b,y,z
    abc_checkem(act[0], act[1], act[2], domsz, delegates, candidates);
    // c,x,y => a,b,c => no a,y,z && no b,y,z
    cxy_checkem(act[0], act[1], act[2], domsz, delegates, candidates);
    // a,y,z => a,b,c => no c,x,y
    ay_checkem(act[0], act[1], domsz, delegates, candidates);
    ay_checkem(act[1], act[0], domsz, delegates, candidates);
  }
}

static
  void
choose_delegate(const unsigned delegate_id,
                BitTable& delegates, BitTable& candidates,
                const SearchOpt& opt)
{
  const UniAct act( UniAct::of_id(delegate_id, opt.domsz) );
  delegates.set1(delegate_id);
  if (opt.nw_commutative) {
    const UniAct dual(act[1], act[0], act[2]);
    const unsigned dual_id = id_of(dual, opt.domsz);
    assert(delegate_id <= dual_id);
    delegates.set1(dual_id);
  }
  trim_coexist(candidates, delegate_id, opt, delegates);
}

static
  void
recurse(Table<BitTable>& delegates_stack,
        Table<BitTable>& candidates_stack,
        uint actid,
        const SearchOpt& opt,
        unsigned depth,
        BitTable& mask)
{
  const uint domsz = opt.domsz;

  BitTable& delegates = delegates_stack[depth];
  BitTable& candidates = candidates_stack[depth];
  delegates = delegates_stack[depth-1];
  candidates = candidates_stack[depth-1];
  choose_delegate(actid, delegates, candidates, opt);

  Table<PcState> ppgfun;
  init_ppgfun(ppgfun, delegates, domsz);
  bool print_delegates = true;
  if (depth == 1 && opt.trust_given) {
    print_delegates = false;
  }
  else {
    switch (periodic_leads_semick(delegates, ppgfun, mask,
                                  candidates_stack, depth, opt)) {
      case Nil: return;
      case May: print_delegates = false;
      case Yes: break;
    }
    if (!canonical_ck(ppgfun, domsz)) {
      return;
    }
  }
  if (print_delegates) {
    oput_b64_ppgfun(*opt.id_ofile, ppgfun, domsz);
    if (opt.line_flush)
      *opt.id_ofile << std::endl;
    else
      *opt.id_ofile << '\n';
  }

  if (depth == opt.max_depth) {
    UniAct act = UniAct::of_id(actid, domsz);
    if (domsz*domsz - 1 - id_of2(act[0], act[1], domsz) <= opt.dfs_threshold) {
      // No return.
    }
    else if (opt.bfs_ofile) {
      oput_b64_ppgfun(*opt.bfs_ofile, ppgfun, domsz);
      if (opt.line_flush)
        *opt.bfs_ofile << std::endl;
      else
        *opt.bfs_ofile << '\n';
      return;
    }
    else {
      return;
    }
  }

  for (uint next_actid = actid+1; next_actid < candidates.sz(); ++next_actid) {
    skip_unless (candidates.ck(next_actid));
    recurse(delegates_stack, candidates_stack,
            next_actid, opt, depth+1, mask);

    // This must be after recurse() so that the livelock
    // detection doesn't remove valid candidates.
    candidates.set0(next_actid);
    if (opt.nw_commutative) {
      UniAct act = UniAct::of_id(next_actid, domsz);
      candidates.set0(id_of(UniAct(act[1], act[0], act[2]), domsz));
    }
  }
}

  void
searchit(const SearchOpt& opt)
{
  const uint domsz = opt.domsz;

  BitTable mask( domsz*domsz*domsz, 0 );
  Table<BitTable> delegates_stack;
  delegates_stack.affysz( domsz*domsz+1, mask );
  BitTable& delegates = delegates_stack[0];

  mask.wipe(1);
  Table<BitTable> candidates_stack;
  candidates_stack.affysz( domsz*domsz+1, mask );
  BitTable& candidates = candidates_stack[0];

  // Remove self-loops.
#define REMOVE_ABB \
  for (uint a = 0; a < domsz; ++a) \
    for (uint b = 0; b < domsz; ++b) \
      candidates.set0(id_of3(a, b, b, domsz))

  // Remove all (a, a, b) actions.
#define REMOVE_AAB \
  for (uint a = 0; a < domsz; ++a) \
    for (uint b = 0; b < domsz; ++b) \
      candidates.set0(id_of3(a, a, b, domsz))

  // Remove all (a, b, a) actions.
#define REMOVE_ABA \
  for (uint a = 0; a < domsz; ++a) \
    for (uint b = 0; b < domsz; ++b) \
      candidates.set0(id_of3(a, b, a, domsz))

#define RECURSE(actid) \
  recurse(delegates_stack, candidates_stack, actid, opt, 1, mask)

  // Never need self-loops.
  REMOVE_ABB;

  if (opt.nw_commutative) {
    REMOVE_AAB;
  }
  if (opt.nw_disabling) {
    REMOVE_ABA;
  }

  if (!opt.given_acts.empty_ck()) {
    unsigned hi_id = 0;
    BitTable tmp_delegates = delegates;
    for (unsigned i = 0; i < opt.given_acts.sz(); ++i) {
      tmp_delegates.set1(id_of(opt.given_acts[i], domsz));
    }
    for (unsigned actid = 0; actid < delegates.sz(); ++actid) {
      if (tmp_delegates.ck(actid) && !delegates.ck(actid)) {
        hi_id = actid;
        choose_delegate(actid, delegates, candidates, opt);
      }
    }
    if (!opt.trust_given &&
        !canonical_ck(uniring_ppgfun_of(delegates, domsz), domsz)) {
      oput_list(std::cerr, uniring_actions_of(mask, domsz));
      failout_sysCx("Assumed a non-canonical set of actions!");
    }

    // Clear out low candidates.
    for (uint actid = 0; actid < hi_id; ++actid) {
      candidates.set0(actid);
      if (opt.nw_commutative) {
        UniAct act = UniAct::of_id(actid, domsz);
        candidates.set0(id_of(UniAct(act[1], act[0], act[2]), domsz));
      }
    }

    Claim( delegates.ck(id_of3(0, 0, 1, domsz)) ||
           delegates.ck(id_of3(0, 1, 0, domsz)) ||
           delegates.ck(id_of3(0, 1, 2, domsz)) );

    if (!delegates.ck(id_of3(0, 0, 1, domsz))) {
      REMOVE_AAB;
      if (!delegates.ck(id_of3(0, 1, 0, domsz))) {
        REMOVE_ABA;
      }
    }

    delegates.set0(hi_id);
    candidates.set1(hi_id);
    if (opt.nw_commutative) {
      UniAct hi_act = UniAct::of_id(hi_id, domsz);
      unsigned dual_id = id_of(UniAct(hi_act[1], hi_act[0], hi_act[2]), domsz);
      delegates.set0(dual_id);
      candidates.set1(dual_id);
    }
    RECURSE(hi_id);
    return;
  }

  if (!opt.nw_commutative) {
    RECURSE(id_of3(0, 0, 1, domsz));
    REMOVE_AAB;
  }

  if (!opt.nw_disabling) {
    RECURSE(id_of3(0, 1, 0, domsz));
    REMOVE_ABA;
  }

  RECURSE(id_of3(0, 1, 2, domsz));

#undef REMOVE_ABB
#undef REMOVE_ABA
#undef REMOVE_AAB_ABA
#undef RECURSE
}

static bool TestKnownAperiodic();

int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);
  SearchOpt opt;

  fildesh::ifstream given_in;
  fildesh::ofstream id_out;

  while (argi < argc) {
    const char* arg = argv[argi++];
    if (eq_cstr ("-domsz", arg)) {
      if (!fildesh_parse_unsigned(&opt.domsz, argv[argi++]) || opt.domsz == 0)
        failout_sysCx("Argument Usage: -domsz <M>\nWhere <M> is a positive integer!");
    }
    else if (eq_cstr ("-bfs", arg)) {
      opt.bfs_ofile = &std::cout;
      if (!fildesh_parse_unsigned(&opt.max_depth, argv[argi++]))
        failout_sysCx("Argument Usage: -bfs <limit>\nWhere <limit> is a nonnegative integer!");
    }
    else if (eq_cstr ("-dfs-within", arg)) {
      // Only positive integers are useful, but let zero slip through.
      if (!fildesh_parse_unsigned(&opt.dfs_threshold, argv[argi++]))
        failout_sysCx("Argument Usage: -dfs-within <threshold>\nWhere <threshold> is a positive integer!");
    }
    else if (eq_cstr ("-o", arg)) {
      arg = argv[argi++];
      id_out.open(arg);
      if (!id_out.good()) {
        failout_sysCx("Argument Usage: -o <file>\nFailed to open the <file>!");
      }
      opt.id_ofile = &id_out;
    }
    else if (eq_cstr ("-max-depth", arg)) {
      if (!fildesh_parse_unsigned(&opt.max_depth, argv[argi++]) || opt.max_depth == 0)
        failout_sysCx("Argument Usage: -max-depth <limit>\nWhere <limit> is a positive integer!");
    }
    else if (eq_cstr("-bound", arg) ||
             eq_cstr("-cutoff", arg)) {
      unsigned cutoff = 0;
      if (!fildesh_parse_unsigned(&cutoff, argv[argi++]) || cutoff == 0)
        failout_sysCx("Argument Usage: -cutoff <limit>\nWhere <limit> is a positive integer!");
      opt.max_period = cutoff;
      opt.max_propagations = cutoff;
    }
    else if (eq_cstr ("-bdd", arg)) {
      opt.use_bdds = true;
    }
    else if (eq_cstr ("-flushoff", arg)) {
      opt.line_flush = false;
    }
    else if (eq_cstr ("-trustme", arg)) {
      opt.trust_given = true;
    }
    else if (eq_cstr ("-max-period", arg)) {
      if (!fildesh_parse_unsigned(&opt.max_period, argv[argi++]) || opt.max_period == 0)
        failout_sysCx("Argument Usage: -max-period <limit>\nWhere <limit> is a positive integer!");
    }
    else if (eq_cstr ("-max-ppgs", arg) ||
             eq_cstr ("-max-propagations", arg)) {
      if (!fildesh_parse_unsigned(&opt.max_propagations, argv[argi++]) || opt.max_propagations == 0)
        failout_sysCx("Argument Usage: -max-ppgs <limit>\nWhere <limit> is a positive integer!");
    }
    else if (eq_cstr ("-nw-disabling", arg)) {
      opt.nw_disabling = true;
    }
    else if (eq_cstr ("-acyclife", arg)) {
      opt.nw_disabling = true;
      opt.nn_ww_disabling = true;
      opt.nw_commutative = true;
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
    else if (eq_cstr ("-init", arg) ||
             eq_cstr ("-id", arg)) {
      if (!argv[argi])
        failout_sysCx("Argument Usage: -init <id>");

      fildesh::istream in(open_FildeshXA());
      size_t n = strlen(argv[argi]);
      memcpy(grow_FildeshX(in.c_struct(), n), argv[argi], n);
      argi += 1;

      Table<PcState> ppgfun;
      opt.domsz = xget_b64_ppgfun(in, ppgfun);
      if (opt.domsz == 0) {
        failout_sysCx (0);
      }
      opt.given_acts = uniring_actions_of(ppgfun, opt.domsz);
    }
    else if (eq_cstr ("-x-init", arg)) {
      if (!argv[argi])
        failout_sysCx("Argument Usage: -x-init <file>");
      given_in.open(argv[argi]);
      if (!given_in.good())
        failout_sysCx("Cannot open init file.");
      argi += 1;

      Table<PcState> ppgfun;
      opt.domsz = xget_b64_ppgfun(given_in, ppgfun);
      if (opt.domsz == 0) {
        failout_sysCx (0);
      }
      opt.given_acts = uniring_actions_of(ppgfun, opt.domsz);
    }
    else  {
      DBog1( "Unrecognized option: %s", arg );
      failout_sysCx (0);
    }
  }

  if (opt.domsz == 0)
    failout_sysCx("Please specify a domain size with the -domsz flag.");

  if (opt.given_acts.sz() > 0) {
    if (opt.max_depth > 0 || opt.bfs_ofile) {
      opt.max_depth += 1;
    }
  }
  opt.commit_domsz();

  while (true) {
    searchit(opt);

    if (!given_in.good())  break;

    Table<PcState> ppgfun;
    uint domsz = xget_b64_ppgfun(given_in, ppgfun);
    if (opt.domsz != domsz) {
      if (domsz == 0)  break;
      failout_sysCx ("Use the same domain size for all inputs.");
    }
    opt.given_acts = uniring_actions_of(ppgfun, opt.domsz);
  }
  lose_sysCx ();
  return 0;
}

  bool
TestKnownAperiodic()
{
  Table<UniAct> acts;
  const uint domsz = tilings_and_patterns_aperiodic_uniring(acts);

  BitTable delegates( domsz*domsz*domsz, 0 );
  for (uint i = 0; i < acts.sz(); ++i) {
    delegates.set1(id_of(acts[i], domsz));
  }

  Table<PcState> ppgfun;
  init_ppgfun(ppgfun, delegates, domsz);

  switch (livelock_semick(15, ppgfun, domsz)) {
    case Nil: DBog0("livelock: Nil");  return false;
    case May: break;
    case Yes: DBog0("livelock: Yes");  return false;
  }

  BitTable mask( domsz*domsz*domsz, 0 );
  const uint depth = acts.sz();
  Table<BitTable> candidates_stack(depth+1, mask);
  SearchOpt opt;
  opt.domsz = domsz;
  opt.max_period = 10;
  opt.check_ppg_overapprox = false;
  opt.commit_domsz();
  switch (periodic_leads_semick(delegates, ppgfun, mask,
                                candidates_stack, depth, opt)) {
    case Nil: DBog0("hard: Nil");  return false;
    case May: DBog0("hard: May");  return false;
    case Yes: break;
  }
  return true;
}


END_NAMESPACE

int main(int argc, char** argv) {
  return PROTOCON_NAMESPACE::main(argc, argv);
}
