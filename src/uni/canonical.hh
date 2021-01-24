#ifndef CANONICAL_HH_
#define CANONICAL_HH_

#include "uniact.hh"
#include "cx/table.hh"

bool
minimal_unique_ck (const uint* a, uint n);
void
permute_pc_act (Cx::Table<PcState>& ppgfun, const Cx::Table<PcState>& choice, const Cx::Table<uint>& perm_map);
bool
canonical_ck(const Cx::Table<PcState>& choice, const uint domsz);

#endif
