

bool fill_livelock_ck(const PcState top[],
                      const uint n,
                      const PcState col[],
                      const uint m,
                      const Table<PcState>& ppgfun,
                      const uint domsz,
                      Table<PcState>& row)
{
  Claim( top[0] == col[0] );
  Claim( top[0] == col[m] );
  Claim( top[0] == top[n] );
  row.ensize(n+1);
  for (uint j = 0; j < n+1; ++j) {
    row[j] = top[j];
  }
  for (uint i = 1; i < m+1; ++i) {
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
  for (PcState diag_val = bot[0]; diag_val < domsz; ++diag_val) {
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
    for (uint j = n; j-- > 0;) {
      skip_unless (bot[j] == bot[n]);
      for (uint i = n; i-- > 0;) {
        skip_unless (col[i] == col[n]);
        if (fill_livelock_ck(&bot[j], bot.sz()-1-j,
                             &col[i], col.sz()-1-i,
                             ppgfun, domsz, ret_row)) {
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

/** Search for a livelock whose periodic block's width and height are bounded.
 **/
  Trit
livelock_semick(const uint limit,
                Table<PcState> ppgfun,
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

    // Remove this value from the next check.
    for (uint a = c; a < domsz; ++a) {
      for (uint b = c; b < domsz; ++b) {
        const uint idx = id_of2(a, b, domsz);
        if (a == c || b == c || ppgfun[idx] == c) {
          ppgfun[idx] = domsz;
        }
      }
    }
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
make_tile_cont_digraph(AdjList<PcState>& digraph, const BitTable& actset,
                       const Table<PcState>& ppgfun, const uint domsz)
{
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
    for each_in_BitTable(actid , actset) {
      const UniAct mid_act = UniAct::of_id(actid, domsz);
      const PcState a = mid_act[0], b = mid_act[1], c = mid_act[2];

      for (PcState d = 0; d < domsz; ++d) {
        const UniAct bot_mask_act(domsz, c, d);
        skip_unless (action_mask_overlap_ck(bot_mask_act, actset, domsz));
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
          skip_unless (action_mask_overlap_ck(next_top_mask_act, actset, domsz));
          // Add arc from this node to the next.
          const Triple<PcState> next(c, e, g);
          const uint next_id = id_of(next, domsz);
          digraph.add_arc(node_id, next_id);
        }
      }
    }
  }
}

  void
make_overapprox_tile_cont_digraph(AdjList<PcState>& digraph,
                                  const BitTable& actset,
                                  const uint domsz)
{
  DoTwice(digraph.commit_degrees()) {
    for each_in_BitTable(actid , actset) {
      const UniAct mid_act = UniAct::of_id(actid, domsz);
      const PcState a = mid_act[0], b = mid_act[1], c = mid_act[2];

      for (PcState d = 0; d < domsz; ++d) {
        const UniAct bot_mask_act(domsz, c, d);
        skip_unless (action_mask_overlap_ck(bot_mask_act, actset, domsz));
        const Triple<PcState> node(a, b, d);
        const uint node_id = id_of(node, domsz);

        for (PcState e = 0; e < domsz; ++e) {
          // Ensure next top tile exists.
          const UniAct next_top_mask_act = UniAct(b, domsz, e);
          skip_unless (action_mask_overlap_ck(next_top_mask_act, actset, domsz));

          for (PcState f = 0; f < domsz; ++f) {
            // Ensure next middle tile exists.
            skip_unless (actset.ck(id_of3(c, e, f, domsz)));

            for (PcState g = 0; g < domsz; ++g) {
              // Ensure next bottom tile exists.
              skip_unless (actset.ck(id_of3(d, f, g, domsz)));

              // Add arc from this node to the next.
              const Triple<PcState> next(c, e, g);
              const uint next_id = id_of(next, domsz);
              digraph.add_arc(node_id, next_id);
            }
          }
        }
      }
    }
  }
}

