

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

