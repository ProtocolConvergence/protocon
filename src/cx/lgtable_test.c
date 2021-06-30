/**
 * \file lgtable_test.c
 **/

#include "syscx.h"

#include "lgtable.h"

/** \test
 * Test the LgTable data structure.
 * Actually, \ref testfn_RBTree() and \ref testfn_Associa() test this better,
 * as they use the structure for memory allocation.
 * This test merely hopes to weed out simple problems before those tests run.
 **/
  void
testfn_LgTable ()
{
  DecloStack1( LgTable, lgt, dflt1_LgTable (sizeof (int)) );
  zuint idx;
  zuint n = 40;
  uint i;

  Claim2( 4 ,==, msb_luint (4) );
  Claim2( 4 ,==, msb_luint (5) );
  Claim2( 8 ,==, msb_luint (13) );

  Claim2( 0 ,==, lg_luint (0) );
  Claim2( 0 ,==, lg_luint (1) );
  Claim2( 1 ,==, lg_luint (2) );
  Claim2( 1 ,==, lg_luint (3) );
  Claim2( 2 ,==, lg_luint (4) );
  Claim2( 2 ,==, lg_luint (4) );

  UFor( i, n ) {
    int* el = (int*) take_LgTable (lgt);
    *el = - (int) i;
    idx = idxelt_LgTable (lgt, el);
    Claim2( idx ,==, i );
  }

  giveidx_LgTable (lgt, 1);
  idx = takeidx_LgTable (lgt);
  Claim2( idx ,==, 1 );

  giveidx_LgTable (lgt, 0);
  idx = takeidx_LgTable (lgt);
  Claim2( idx ,==, 0 );

  giveidx_LgTable (lgt, 5);
  idx = takeidx_LgTable (lgt);
  Claim2( idx ,==, 5 );

  giveidx_LgTable (lgt, 7);
  idx = takeidx_LgTable (lgt);
  Claim2( idx ,==, 7 );

  UFor( i, n ) {
    zuint sz = n-i;
    Claim2( lgt->allocs.sz ,<=, (zuint) lg_luint (sz) + 2 );
    giveidx_LgTable (lgt, sz-1);
  }

  lose_LgTable (lgt);
}

/** \test
 * Stress test of the LgTable data structure.
 **/
static
  void
testfn_stress_LgTable ()
{
  const uint n = 1e5;
  LgTable lgt[1];
  uint i;
  *lgt = dflt1_LgTable (sizeof(int));

  UFor( i, n ) {
    uint nallocs;
    uint idx;
    idx = takeidx_LgTable (lgt);
    Claim2( idx ,==, i );
    nallocs = lgt->allocs.sz;
    giveidx_LgTable (lgt, i);
    Claim2( nallocs ,==, lgt->allocs.sz );
    idx = takeidx_LgTable (lgt);
    Claim2( idx ,==, i );
    Claim2( nallocs ,==, lgt->allocs.sz );
  }

  UFor( i, n ) {
    giveidx_LgTable (lgt, n-i-1);
    if (lgt->sz >= 2)
      Claim2( 8 * lgt->sz / 3 ,>, allocsz_of_LgTable (lgt) );
    else
      Claim2( allocsz_of_LgTable (lgt) ,==, 4);

    if (i > n / 2) {
      Claim2( 4 * lgt->sz / 3 ,<=, allocsz_of_LgTable (lgt) );
    }
  }
  Claim2( lgt->sz ,==, 0 );
  Claim2( allocsz_of_LgTable (lgt) ,==, 4 );

  UFor( i, n ) {
    takeidx_LgTable (lgt);
  }
  UFor( i, n ) {
    giveidx_LgTable (lgt, i);
  }
  Claim2( lgt->sz ,==, 0 );
  Claim2( allocsz_of_LgTable (lgt) ,==, 4 );

  lose_LgTable (lgt);
}

int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);
  (void) argi;

  testfn_LgTable();
  testfn_stress_LgTable();

  lose_sysCx ();
  return 0;
}
