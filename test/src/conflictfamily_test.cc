
#include "src/conflictfamily.hh"
#include "src/cx/lgtable.hh"

#include "src/namespace.hh"

static
  void
TestConflictFamily()
{
  ConflictFamily conflicts;
  LgTable< Set<uint> > delsets;

  delsets.grow1() <<  0 <<  1 <<  3;
  delsets.grow1() <<  5 <<  1 <<  3;
  delsets.grow1() <<  7 <<  1 <<  3;
  delsets.grow1() << 11 <<  1 <<  3;
  delsets.grow1() << 14 << 15 <<  1 << 3;
  delsets.grow1() << 14 << 17 <<  1 << 3;
  for (uint i = 0; i < delsets.sz(); ++i)
    conflicts.add_conflict(delsets[i]);

  Set<uint> action_set;
  action_set << 1 << 3 << 2 << 16 << 20;
  Set<uint> candidate_set;
  candidate_set << 5 << 0 << 14 << 17;

  Set<uint> membs;
  bool good =
    conflicts.conflict_membs(&membs, FlatSet<uint>(action_set),
                             FlatSet<uint>(candidate_set));
  Claim( good );
  Claim( membs.elem_ck(5) );
  Claim( membs.elem_ck(0) );
  Claim( !membs.elem_ck(7) );
  Claim( !membs.elem_ck(14) );
  Claim( !membs.elem_ck(15) );
  Claim( !membs.elem_ck(17) );

  candidate_set -= membs;
  membs.clear();
  good =
    conflicts.conflict_membs(&membs, FlatSet<uint>(action_set),
                             FlatSet<uint>(candidate_set));
  Claim( good );
  Claim( membs.empty() );

  conflicts.add_conflict( Set<uint>() << 1 << 3 << 16 );
  good =
    conflicts.conflict_membs(&membs, FlatSet<uint>(action_set),
                             FlatSet<uint>(candidate_set));
  Claim( !good );
}

END_NAMESPACE

int main() {
  using namespace PROTOCON_NAMESPACE;
  TestConflictFamily();
  return 0;
}

