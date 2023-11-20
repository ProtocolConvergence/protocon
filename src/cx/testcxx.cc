
#include "table.hh"
#include "lgtable.hh"
#include "set.hh"

/**
 * Test dat code.
 */
  void
testfn_CXX_Table()
{
  Cx::Table<uint> t;
  t.push(1);
  t.push(2);
  Claim2_uint( t[1] ,==, 2 );
  Claim2_uint( t[0] ,==, 1 );
}

/**
 * Test dat code.
 */
  void
testfn_CXX_LgTable()
{
  Cx::LgTable<uint> t;
  t.push(1);
  t.push(2);
  Claim2_uint( t[1] ,==, 2 );
  Claim2_uint( t[0] ,==, 1 );
}

  void
testfn_CXX_FlatSet()
{
  Cx::Table<uint> tab_b;
  tab_b.push(3);
  tab_b.push(2);
  tab_b.push(7);
  tab_b.push(11);
  tab_b.push(4);
  tab_b.push(6);
  tab_b.push(15);
  tab_b.push(0);

  Cx::Set<uint> set_b(tab_b);
  Cx::FlatSet<uint> flat_a( tab_b );
  Claim( flat_a.elem_ck(3) );
  Claim( flat_a.elem_ck(15) );

  {
    Cx::FlatSet<uint> flat_b( tab_b );
    Claim( flat_a.subseteq_ck(flat_b) );
    Claim( flat_b.subseteq_ck(flat_a) );
  }
  set_b << 50;
  {
    Cx::FlatSet<uint> flat_b( set_b );
    Claim( flat_a.subseteq_ck(flat_b) );
    Claim( !flat_b.subseteq_ck(flat_a) );
  }
  set_b -= Set<uint>(50);
  set_b << 10;
  {
    Cx::FlatSet<uint> flat_b( set_b );
    Claim( flat_a.subseteq_ck(flat_b) );
    Claim( !flat_b.subseteq_ck(flat_a) );
  }
}

int main() {
  testfn_CXX_Table();
  testfn_CXX_LgTable();
  testfn_CXX_FlatSet();
  return 0;
}

