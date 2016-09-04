
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

