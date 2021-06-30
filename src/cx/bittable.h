/**
 * \file bittable.h
 **/
#ifndef BitTable_H_
#define BitTable_H_

#include "table.h"

#include <assert.h>

DeclTableT( Bit, unsigned int );

typedef TableT(Bit) BitTable;
typedef TableElT(Bit) BitTableEl;
#define NBits_BitTableEl  (sizeof (BitTableEl) * BYTE_BIT)

#define FixDeclBitTable( bt, n, val ) \
  BitTableEl DeclBitTable_##bt[CeilQuot( n, NBits_BitTableEl )]; \
  BitTable bt = dflt3_BitTable( n, DeclBitTable_##bt, val )

#define LowBitMaskT( T, n ) \
  ((T) (((n)==0) ? 0 : ~(~(T)1 << ((n)-1))))

#define BitMaskT( T, i, n ) \
  ((T) (LowBitMaskT(T, n) << (i)))

#define LowBits( x, nbits ) \
  ((x) & ~(((x) | ~(x)) << (nbits)))

#define Bits4LH( b00, b01, b10, b11 ) \
  ((b00 << 0) | (b01 << 1) | (b10 << 2) | (b11 << 3))

enum BitOp {
  /*           a = 0011 */
  /*           b = 0101 */
  BitOp_NIL   = /* 0000 */ Bits4LH(0,0,0,0),
  BitOp_NOR   = /* 1000 */ Bits4LH(1,0,0,0),
  BitOp_NOT1  = /* 1100 */ Bits4LH(1,1,0,0),
  BitOp_NIMP  = /* 0010 */ Bits4LH(0,0,1,0),
  BitOp_NOT0  = /* 1010 */ Bits4LH(1,0,1,0),
  BitOp_XOR   = /* 0110 */ Bits4LH(0,1,1,0),
  BitOp_NAND  = /* 1110 */ Bits4LH(1,1,1,0),
  BitOp_AND   = /* 0001 */ Bits4LH(0,0,0,1),
  BitOp_XNOR  = /* 1001 */ Bits4LH(1,0,0,1),
  BitOp_IDEN1 = /* 0101 */ Bits4LH(0,1,0,1),
  BitOp_IMP   = /* 1101 */ Bits4LH(1,1,0,1),
  BitOp_IDEN0 = /* 0011 */ Bits4LH(0,0,1,1),
  BitOp_OR    = /* 0111 */ Bits4LH(0,1,1,1),
  BitOp_YES   = /* 1111 */ Bits4LH(1,1,1,1),
  NBitOps
};
typedef enum BitOp BitOp;


/** Most significant 1 bit.**/
qual_inline
  bitint
msb_luint (luint x)
{
  bitint i;
  for (i = 1; i < LONG_BIT; i *= 2)
    x |= (x >> i);
  return (x & ~(x >> 1));
}

/** Least significant 1 bit.**/
qual_inline
  luint
lsb_luint (luint x)
{
  return (x & (~x + 1));
}

/** Least significant 1 bit.**/
qual_inline
  BitTableEl
lsb_BitTableEl (BitTableEl x)
{
  return (x & (~x + 1));
}

/** Floor of the lg (log base 2) of some integer.
 * - 0..1 -> 0
 * - 2..3 -> 1
 * - 4..7 -> 2
 * - 8..15 -> 3
 * - 16..31 -> 4
 * - 32..63 -> 5
 * - 64..127 -> 6
 **/
qual_inline
  bitint
lg_luint (luint x)
{
  bitint i;
  bitint n = 0;
  for (i = msb_luint (LONG_BIT-1); i > 0; i /= 2)
  {
    luint y = (x >> i);
    n *= 2;
    if (y != 0)
    {
      n += 1;
      x = y;
    }
  }
  return n;
}


#define DeclBitTableIdcs( p, q, i ) \
  const zuint p = (i) / NBits_BitTableEl; \
  const uint  q = (i) % NBits_BitTableEl

qual_inline
  void
wipe_BitTable (BitTable bt, Bit val)
{
  const zuint n = CeilQuot( bt.sz, NBits_BitTableEl );
  memset (bt.s,
      (val == 0) ? 0x00 : 0xFF,
      n * sizeof (BitTableEl));
}

#define DEFAULT_BitTable DEFAULT_Table
qual_inline
  BitTable
dflt_BitTable ()
{
  BitTable bt = DEFAULT_BitTable;
  return bt;
}

qual_inline
  BitTable
dflt2_BitTable (zuint nbits, BitTableEl* s)
{
  BitTable bt = DEFAULT_BitTable;
  bt.s = s;
  bt.sz = nbits;
  return bt;
}

qual_inline
  BitTable
dflt3_BitTable (zuint nbits, BitTableEl* s, Bit val)
{
  BitTable bt = dflt2_BitTable (nbits, s);
  wipe_BitTable (bt, val);
  return bt;
}

qual_inline
  BitTable
cons1_BitTable (zuint n)
{
  const zuint nblocks = CeilQuot( n, NBits_BitTableEl );
  BitTable bt = DEFAULT_BitTable;
  GrowTable( bt, nblocks );
  bt.sz = n;
  return bt;
}

qual_inline
  BitTable
cons2_BitTable (zuint n, Bit val)
{
  BitTable bt = cons1_BitTable (n);

  if (bt.s)
    wipe_BitTable (bt, val);

  return bt;
}

qual_inline
  void
lose_BitTable (BitTable* bt)
{
  LoseTable( *bt );
}

qual_inline
  void
size_fo_BitTable (BitTable* bt, zuint n)
{
  const zuint sz = bt->sz;
  const zuint new_sz = n;
  const zuint nelems = CeilQuot( sz, NBits_BitTableEl );
  const zuint new_nelems = CeilQuot( new_sz, NBits_BitTableEl );
  bt->sz = nelems;
  SizeTable( *bt, new_nelems );
  if (new_nelems > nelems)
    memset (&bt->s[nelems], 0,
        (new_nelems - nelems) * sizeof (BitTableEl));
  bt->sz = new_sz;
}

qual_inline
  void
size_BitTable (BitTable* bt, zuint n)
{
  size_fo_BitTable (bt, n);
}

qual_inline
  void
grow_BitTable (BitTable* bt, zuint n)
{
  size_BitTable (bt, bt->sz+n);
}

qual_inline
  void
mpop_BitTable (BitTable* bt, zuint n)
{
  size_BitTable (bt, bt->sz - n);
}


/** Test if a bit is set (to one).**/
qual_inline
  Bit
test_BitTable (const BitTable bt, zuint i)
{
  DeclBitTableIdcs( p, q, i );
  return (0 != (bt.s[p] & (1 << q)));
}

/** Check if a bit is set (to one).**/
qual_inline
  Bit
chk_BitTable (const BitTable bt, zuint i)
{
  DeclBitTableIdcs( p, q, i );
  return (0 != (bt.s[p] & (1 << q)));
}

/** Check if a bit is set (to one).**/
qual_inline
  Bit
ck_BitTable (const BitTable bt, zuint i)
{
  DeclBitTableIdcs( p, q, i );
  return (0 != (bt.s[p] & (1 << q)));
}

/** Set a bit to one.**/
qual_inline
  Bit
set1_BitTable (BitTable bt, zuint i)
{
  DeclBitTableIdcs( p, q, i );
  const BitTableEl x = bt.s[p];
  const BitTableEl y = 1 << q;

  if (0 != (x & y))
  {
    return 1;
  }
  else
  {
    bt.s[p] = x | y;
    return 0;
  }
}

/** Set a bit to zero.**/
qual_inline
  Bit
set0_BitTable (BitTable bt, zuint i)
{
  DeclBitTableIdcs( p, q, i );
  const BitTableEl x = bt.s[p];
  const BitTableEl y = 1 << q;

  if (0 == (x & y))
  {
    return 0;
  }
  else
  {
    bt.s[p] = x & ~y;
    return 1;
  }
}

/** Set a bit.
 * \sa set0_BitTable()
 * \sa set1_BitTable()
 **/
qual_inline
  Bit
setb_BitTable (BitTable bt, zuint i, Bit b)
{
  return (b ? set1_BitTable (bt, i) : set0_BitTable (bt, i));
}

/** Set a bit to one.**/
qual_inline
  void
set_uint_BitTable (BitTable bt, const zuint i, const uint nbits, const uint z)
{
  uint off = 0;
  while (off < nbits && i+off < bt.sz) {
    DeclBitTableIdcs( p, q, i+off );
    const BitTableEl x = bt.s[p];
    const uint n = (q + (nbits - off) > NBits_BitTableEl)
      ? NBits_BitTableEl - q
      : nbits - off;
    const uint mask = BitMaskT( uint, q, n );

    bt.s[p] = (x & ~mask) | (((z >> off) << q) & mask);
    off += n;
    if (i+off >= bt.sz)
      return;
  }
}

qual_inline
  uint
get_uint_BitTable (BitTable bt, const zuint i, const uint nbits)
{
  uint off = 0;
  uint z = 0;
  while (off < nbits && i+off < bt.sz) {
    DeclBitTableIdcs( p, q, i+off );
    const BitTableEl x = bt.s[p];
    uint n = (q + (nbits - off) > NBits_BitTableEl)
      ? NBits_BitTableEl - q
      : nbits - off;

    z |= ((x & BitMaskT( uint, q, n )) >> q) << off;
    off += n;
  }
  return z;
}

#define Do_BitOp_NIL(a,b)  (0)
#define Do_BitOp_NOR(a,b)  (~(a) | (b))
#define Do_BitOp_NOT1(a,b)  (~(b))
#define Do_BitOp_NIMP(a,b)  ((a) & ~(b))
#define Do_BitOp_NOT0(a,b)  (~(a))
#define Do_BitOp_XOR(a,b)  ((a) ^ (b))
#define Do_BitOp_NAND(a,b)  (~(a) & (b))
#define Do_BitOp_AND(a,b)  ((a) & (b))
#define Do_BitOp_XNOR(a,b)  (~(a) ^ (b))
#define Do_BitOp_IDEN1(a,b)  (b)
#define Do_BitOp_IMP(a,b)  (~(a) | (b))
#define Do_BitOp_IDEN0(a,b)  (a)
#define Do_BitOp_OR(a,b)  ((a) | (b))
#define Do_BitOp_YES(a,b)  (1)

qual_inline
  void
op2_BitTable (BitTable* c, BitOp op, const BitTable a, const BitTable b)
{
  zuint i;
  const zuint n = CeilQuot( a.sz, NBits_BitTableEl );

  Claim2( a.sz ,==, b.sz );
  size_fo_BitTable (c, a.sz);

#define DoCase( OP ) \
  case BitOp_##OP: \
                   UFor( i, n )  c->s[i] = Do_BitOp_##OP( a.s[i], b.s[i] ); \
  break

  switch (op)
  {
    case BitOp_NIL:
      wipe_BitTable (*c, 0);
      break;
      DoCase( NOR );
      DoCase( NOT1 );
      DoCase( NIMP );
      DoCase( NOT0 );
      DoCase( XOR );
      DoCase( NAND );
      DoCase( AND );
      DoCase( XNOR );
    case BitOp_IDEN1:
      if (c->s != b.s)  memcpy (c->s, b.s, n * sizeof (BitTableEl));
      break;
      DoCase( IMP );
    case BitOp_IDEN0:
      if (c->s != a.s)  memcpy (c->s, a.s, n * sizeof (BitTableEl));
      break;
      DoCase( OR );
    case BitOp_YES:
      wipe_BitTable (a, 1);
      break;
    case NBitOps:
      Claim(0);
      break;
  }

#undef DoCase
}

qual_inline
  void
op_BitTable (BitTable a, BitOp op, const BitTable b)
{
  Claim2( a.sz ,==, b.sz );
  op2_BitTable (&a, op, a, b);
}

qual_inline
  Bit
fold_map2_BitTable (BitOp fold_op, BitOp map_op, const BitTable a, const BitTable b)
{
  zuint i;
  DeclBitTableIdcs( n, q, a.sz );
  BitTableEl conj = 0;
  BitTableEl disj = 0;
  conj = ~conj;

  Claim2( a.sz ,==, b.sz );

#define DoCase( OP ) \
  case BitOp_##OP: \
                   UFor( i, n ) \
  { \
    BitTableEl c = Do_BitOp_##OP( a.s[i], b.s[i] ); \
    conj &= c; \
    disj |= c; \
  } \
  if (q != 0) \
  { \
    BitTableEl c = Do_BitOp_##OP( a.s[n], b.s[n] ); \
    conj &= BitMaskT(BitTableEl, q, NBits_BitTableEl) | c; \
    disj |= LowBits(c, q); \
  } \
  break

  switch (map_op)
  {
    case BitOp_NIL:
      conj = 0;
      break;
      DoCase( NOR );
      DoCase( NOT1 );
      DoCase( NIMP );
      DoCase( NOT0 );
      DoCase( XOR );
      DoCase( NAND );
      DoCase( AND );
      DoCase( XNOR );
      DoCase( IDEN1 );
      DoCase( IMP );
      DoCase( IDEN0 );
      DoCase( OR );
    case BitOp_YES:
      disj = ~disj;
      break;
    case NBitOps:
      Claim(0);
      break;
  }
#undef DoCase

  switch (fold_op)
  {
    case BitOp_AND:
      return ~conj == 0 ? 1 : 0;
    case BitOp_OR:
      return  disj == 0 ? 0 : 1;
    default:
      Claim(0);
      break;
  }
  return 0;
}

qual_inline
  Bit
all_BitTable (const BitTable bt)
{
  DeclBitTableIdcs( p, q, bt.sz );
  zuint i;

  UFor( i, p )
    if (0 != ~ bt.s[i])
      return 0;

  UFor( i, q )
    if (!ck_BitTable (bt, bt.sz - 1 - i))
      return 0;

  return 1;
}

qual_inline
  Bit
sat_ck_BitTable (const BitTable bt)
{
  DeclBitTableIdcs( p, q, bt.sz );
  zuint i;

  UFor( i, p )
    if (0 != bt.s[i])
      return 0;

  UFor( i, q )
    if (ck_BitTable (bt, bt.sz - 1 - i))
      return 0;

  return 1;
}

qual_inline
  Sign
cmp_BitTableEl (const BitTableEl a, const BitTableEl b)
{
  BitTableEl no_a, no_b;
  if (a == b)  return 0;
  no_a = (~a & b);
  no_b = (~b & a);
  if (no_a == 0)  return  1;
  if (no_b == 0)  return -1;
  return
    (lsb_BitTableEl (no_a) < lsb_BitTableEl (no_b)) ? -1 : 1;
}

qual_inline
  Sign
cmp_BitTable (const BitTable a, const BitTable b)
{
  Sign sign;
  const zuint n = (a.sz <= b.sz) ? a.sz : b.sz;
  DeclBitTableIdcs( p, q, n );
  zuint i;

  for (i = 0; i < p; ++i)
  {
    sign = cmp_BitTableEl (a.s[i], b.s[i]);
    if (sign != 0)
      return sign;
  }

  if (q > 0) {
    sign = cmp_BitTableEl (LowBits(a.s[p], q), LowBits(b.s[p], q));
    if (sign != 0)
      return sign;
  }
  if (a.sz == b.sz)  return 0;
  return ((a.sz < b.sz) ? -1 : 1);
}
#undef DeclBitTableIdcs

qual_inline
  zuint
nextidx_BitTable (const BitTable bt, zuint idx)
{
  while (++idx < bt.sz)
    if (ck_BitTable (bt, idx))
      return idx;
  return idx;
}

qual_inline
  zuint
begidx_BitTable (const BitTable bt)
{
  if (bt.sz == 0)  return SIZE_MAX;
  if (ck_BitTable (bt, 0))  return 0;
  return nextidx_BitTable (bt, 0);
}

qual_inline
  zuint
next_BitTable (const BitTable bt, zuint idx)
{
  while (++idx < bt.sz)
    if (ck_BitTable (bt, idx))
      return idx;
  return SIZE_MAX;
}

qual_inline
  zuint
beg_BitTable (const BitTable bt)
{
  if (bt.sz == 0)  return SIZE_MAX;
  if (ck_BitTable (bt, 0))  return 0;
  return next_BitTable (bt, 0);
}

qual_inline
  zuint
count_BitTable (const BitTable bt)
{
  zuint n = 0;
  zuint i;
  for (i = begidx_BitTable (bt);
      i < bt.sz;
      i = nextidx_BitTable (bt, i))
    ++n;
  return n;
}

#endif

