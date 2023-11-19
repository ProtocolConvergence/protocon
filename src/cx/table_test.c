/**
 * \file table_test.c
 * Tests for dynamic arrays.
 **/

#include "syscx.h"

#include "alphatab.h"


static
  void
claim_allocsz_Table (Table* t)
{
  const zuint sz = t->sz;
  const zuint allocsz = allocsz_Table (t);

  Claim2( sz ,<=, allocsz );
  Claim2( sz ,>=, allocsz / 4 );

  if (sz <= allocsz / 2) {
    grow_Table (t, allocsz / 2);
    Claim2( allocsz ,==, allocsz_Table (t) );
    mpop_Table (t, allocsz / 2);
    Claim2( allocsz ,==, allocsz_Table (t) );
  }

  if (sz >= allocsz / 2) {
    mpop_Table (t, allocsz / 4);
    Claim2( allocsz ,==, allocsz_Table (t) );
    grow_Table (t, allocsz / 4);
    Claim2( allocsz ,==, allocsz_Table (t) );
  }

  if (sz < allocsz / 2 && sz > 0) {
    mpop_Table (t, CeilQuot( sz, 2 ));
    Claim2( allocsz / 2 ,==, allocsz_Table (t) );
    grow_Table (t, CeilQuot( sz, 2 ));
    Claim2( allocsz / 2 ,==, allocsz_Table (t) );

    /* Get allocsz back.*/
    grow_Table (t, allocsz / 2);
    Claim2( allocsz ,==, allocsz_Table (t) );
    mpop_Table (t, allocsz / 2);
    Claim2( allocsz ,==, allocsz_Table (t) );
  }
  else if (sz > allocsz / 2) {
    grow_Table (t, sz);
    Claim2( allocsz * 2 ,==, allocsz_Table (t) );
    mpop_Table (t, sz);
    Claim2( allocsz * 2 ,==, allocsz_Table (t) );

    /* Get allocsz back.*/
    mpop_Table (t, sz / 2 + 1);
    Claim2( allocsz ,==, allocsz_Table (t) );
    grow_Table (t, sz / 2 + 1);
    Claim2( allocsz ,==, allocsz_Table (t) );
  }

  Claim2( sz ,==, t->sz );
  Claim2( allocsz ,==, allocsz_Table (t));
}

/** \test
 * Rigorously test Table structure.
 * At each push/pop step, assertions are made about when the table should
 * resize. This ensures the Table has proper a proper amortized constant
 * cost.
 **/
  void
testfn_Table ()
{
  const int val = 7;
  uint n = (1 << 12) + 1;
  DeclTableT( V, int );
  DeclTable( V, t );
  Table tmp_table;
  uint i;

  tmp_table = MakeCastTable( t );
  claim_allocsz_Table (&tmp_table);
  XferCastTable( t, tmp_table );

  for (i = 0; i < n; ++i) {
    DeclGrow1Table( V, x, t );
    *x = (int) i;

    tmp_table = MakeCastTable( t );
    claim_allocsz_Table (&tmp_table);
    XferCastTable( t, tmp_table );
  }

  PackTable( t );
  Claim2( t.sz - 1 ,==, AllocszTable( t ));

  for (i = 0; i < n; ++i) {
    t.s[t.sz-1] = val;
    MPopTable( t, 1 );

    tmp_table = MakeCastTable( t );
    claim_allocsz_Table (&tmp_table);
    XferCastTable( t, tmp_table );
  }

  Claim2( 0 ,==, t.sz );
  Claim2( 0 ,<, AllocszTable( t ));
  PackTable( t );
  Claim2( 0 ,==, AllocszTable( t ));
  InitTable( t );

  PushTable( t, val );
  Claim2( 1 ,==, t.sz );
  PackTable( t );
  PushTable( t, val );
  GrowTable( t, 10 );
  MPopTable( t, 12 );


  PushTable( t, val );
  PushTable( t, val );
  PushTable( t, val );
  Claim2( 3 ,==, t.sz );
  LoseTable( t );
}


int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);
  (void) argi;

  testfn_Table();

  lose_sysCx ();
  return 0;
}
