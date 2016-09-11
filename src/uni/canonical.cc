
static
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

static
  void
permute_pc_act (Table<PcState>& ppgfun, const Table<PcState>& choice, const Table<uint>& perm_map)
{
  const uint domsz = perm_map.sz();
  ppgfun.wipe(domsz);
  for (uint a = 0; a < domsz; ++a) {
    for (uint b = 0; b < domsz; ++b) {
      uint c = choice[id_of2(a, b, domsz)];
      skip_unless (c < domsz);
      ppgfun[id_of2(perm_map[a], perm_map[b], domsz)] = perm_map[c];
    }
  }
}

  bool
canonical_ck(const Table<PcState>& choice, const uint domsz)
{
  Table<uint> perm_doms(domsz-1);
  luint nperms = 1;
  for (uint i = 2; i <= domsz; ++i) {
    perm_doms[i-2] = i;
    nperms *= perm_doms[i-2];
  }
  Table<uint> perm_vals(domsz-1);
  Table<uint> perm_map(domsz);

  Table<PcState> ppgfun(domsz*domsz, domsz);

  for (luint perm_idx = 0; perm_idx < nperms; ++perm_idx) {
    state_of_index (&perm_vals[0], perm_idx, perm_doms);
    for (uint i = 0; i < domsz; ++i) {
      perm_map[i] = i;
    }
    for (uint i = 0; i < perm_vals.sz(); ++i) {
      SwapT( uint, perm_map[i], perm_map[perm_vals[i]] );
    }
#if 0
    Claim( minimal_unique_ck(&perm_map[0], perm_map.sz()) );
#else
    (void) minimal_unique_ck;
#endif
    permute_pc_act (ppgfun, choice, perm_map);
    if (ppgfun < choice) {
      return false;
    }
  }
  return true;
}

