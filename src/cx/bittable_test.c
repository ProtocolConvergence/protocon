/**
 * \file bittable_test.c
 * Tests for bitstrings of 0 and 1.
 **/

#include "syscx.h"

#include "bittable.h"


/** \test
 * Set and test at a bunch of indices.
 **/
static
  void
testfn_BitTable ()
{
  uint n = 1000;
  uint ni = CeilQuot( n, 3 );
  BitTable bt = cons2_BitTable (n, 0);
  uint i;

  UFor( i, ni ) {
    Bit x;
    x = set1_BitTable (bt, 3 * i);
    Claim2( x ,==, 0 );
  }

  UFor( i, n ) {
    Bit x, y;
    x = test_BitTable (bt, i);
    y = (0 == (i % 3));
    Claim2( x ,==, y );
    x = set1_BitTable (bt, i);
    Claim2( x ,==, y );
  }

  {
    Claim2( (1<<4) | (1<<3) ,==, BitMaskT(uint, 3, 2) );
    Claim2( (1<<5) | (1<<4) | (1<<3) ,==, BitMaskT(uint, 3, 3) );
    set_uint_BitTable(bt, 3, 3, 5);
    Claim2( 5 ,==, get_uint_BitTable(bt, 3, 3) );
    Claim2( 1 ,==, get_uint_BitTable(bt, 3, 2) );
  }

  {
    const uint idx = INT_BIT - 2;
    const uint x = 100;
    set_uint_BitTable(bt, idx, 5, x);
    Claim2( x & 7        ,==, get_uint_BitTable(bt, idx  , 3) );
    Claim2( (x >> 1) & 7 ,==, get_uint_BitTable(bt, idx+1, 3) );
    Claim2( x & 15       ,==, get_uint_BitTable(bt, idx  , 4) );
    Claim2( x & 31       ,==, get_uint_BitTable(bt, idx  , 5) );
  }

  lose_BitTable (&bt);
}

/** \test
 * This mimics the dirty bit in a set associative cache,
 * but is unrealistic since it disregards any values.
 * Now, if all values fall inside [0..255], then we have a useful tool,
 * but then LowBits() would not be tested.
 **/
static
  void
testfn_cache_BitTable ()
{
  uint i;
  Bit flag;
  FixDeclBitTable( cache, 256, 1 );
  const uint nslots = cache.sz;
  const uint nbits = 8;

  UFor( i, nslots )
    Claim( test_BitTable (cache, i) );
  set0_BitTable (cache, 100);
  wipe_BitTable (cache, 0);
  UFor( i, nslots )
    Claim( !test_BitTable (cache, i) );

  i = LowBits( nslots+1, nbits );
  Claim2( i ,==, 1 );
  flag = set1_BitTable (cache, i);
  Claim2( flag ,==, 0 );

  i = LowBits( nslots-1, nbits );
  Claim2( i ,==, nslots-1 );
  flag = set1_BitTable (cache, i);
  Claim2( flag ,==, 0 );

  i = LowBits( 3*(nslots-1), nbits );
  Claim2( i ,==, nslots-3 );
  flag = set1_BitTable (cache, i);
  Claim2( flag ,==, 0 );

  i = LowBits( 5*nslots-3, nbits );
  Claim2( i ,==, nslots-3 );
  flag = set1_BitTable (cache, i);
  Claim2( flag ,==, 1 );
}


int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);
  (void) argi;

  testfn_BitTable();
  testfn_cache_BitTable();

  lose_sysCx ();
  return 0;
}
