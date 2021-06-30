
#include "bittable.h"
#include "urandom.h"

/** If our uint32 type is more than 32 bits, then this mask
 * should be applied to ensure overflowing sums are truncated.
 * But uint32_t should be 32 bits, so it isn't used.
 **/
#define MASK32(x)  (UINT32_MAX & (x))
#define MASK16(x)  (UINT16_MAX & (x))


/** Chris Lomont's random number generator.
 * From: http://stackoverflow.com/a/1227137/5039395
 * http://lomont.org/papers/2008/Lomont_PRNG_2008.pdf
 **/
qual_inline
  uint32_t
uint32_WELL512 (URandom* ctx)
{
  uint32_t* state = ctx->state;
#define index  ctx->state[16]
  uint32_t a, b, c, d;
  a = state[index];
  c = state[(index+13)&15];
  b = a^c^(a<<16)^(c<<15);
  c = state[(index+9)&15];
  c ^= (c>>11);
  a = state[index] = b^c;
  d = a^((a<<5)&0xDA442D24UL);
  index = (index + 15)&15;
  a = state[index];
  state[index] = a^b^d^(a<<2)^(b<<18)^(c<<28);
  return state[index];
}

qual_inline
  void
init_WELL512 (URandom* ctx)
{
  index = 0;
#undef index
}


/** 32-bit hash function from Thomas Wang.
 *
 * Found here: http://burtleburtle.net/bob/hash/integer.html
 **/
qual_inline
  uint32_t
uint32_hash_ThomasWang (uint32_t a)
{
  a = (a ^ 61) ^ (a >> 16);
  a = a + (a << 3);
  a = a ^ (a >> 4);
  a = a * 0x27d4eb2d;
  a = a ^ (a >> 15);
  return a;
}
#define uint32_hash uint32_hash_ThomasWang


/** 64-bit hash function from Thomas Wang.
 *
 * Found here: https://naml.us/blog/tag/thomas-wang
 **/
qual_inline
  uint64_t
uint64_hash_ThomasWang(uint64_t key)
{
  key = (~key) + (key << 21); /* key = (key << 21) - key - 1;*/
  key = key ^ (key >> 24);
  key = (key + (key << 3)) + (key << 8); /* key * 265 */
  key = key ^ (key >> 14);
  key = (key + (key << 2)) + (key << 4); /* key * 21 */
  key = key ^ (key >> 28);
  key = key + (key << 31);
  return key;
}


  void
init2_seeded_URandom (URandom* urandom, uint pcidx, uint npcs)
{
  (void) npcs;
  init_WELL512 (urandom);
  /* init_GMRand (urandom); */
  urandom->salt = uint32_hash(pcidx);
}

  void
init3_URandom (URandom* urandom, uint pcidx, uint npcs, uint seed)
{
  uint i;
  (void) npcs;
  for (i = 0; i < ArraySz(urandom->state); ++i) {
    uint32 x = seed + i + ArraySz(urandom->state) * pcidx;
    urandom->state[i] = uint32_hash(x);
  }

  init2_seeded_URandom (urandom, pcidx, npcs);
}

  void
init2_URandom (URandom* urandom, uint pcidx, uint npcs)
{
  uint i;
  (void) npcs;
  for (i = 0; i < ArraySz(urandom->state); ++i) {
    uint32 x = i + ArraySz(urandom->state) * pcidx;
    urandom->state[i] = uint32_hash(x);
  }

  Randomize( urandom->state );
  init2_seeded_URandom (urandom, pcidx, npcs);
}

  void
init1_URandom (URandom* urandom, uint seed)
{
  init3_URandom (urandom, 0, 1, seed);
}

  uint32
uint32_URandom (URandom* urandom)
{
  uint32 x = uint32_WELL512 (urandom);
  /* uint32 x = uint32_GMRand (urandom); */
  return (x ^ urandom->salt);
}

  Bit
bit_URandom (URandom* urandom)
{
  return (Bit) (uint32_URandom (urandom) >> 31);
}

/** Generate a uint in {0,...,n-1}.**/
  uint
uint_URandom (URandom* urandom, uint n)
{
#if 1
  uint x = uint32_URandom (urandom);
  return (uint) (n * (x * 2.328306e-10));
#else
  /* May screw with the randomness.*/
  const uint32 q = (UINT32_MAX / n);
  const uint32 m = UINT32_MAX - (UINT32_MAX % n);
  uint32 x;
  do {
    x = uint32_URandom (a);
  } while (x >= m);
  return x / q;
#endif
}


/** Shuffle integers in an array.**/
  void
shuffle_uints_URandom (URandom* urandom, uint* a, uint n)
{
  for (; n > 1; --n)
  {
    uint i = n-1;
    uint j = uint_URandom (urandom, n);
    SwapT( uint, a[i], a[j] );
  }
}

  uint
randommod_sysCx(uint n)
{
  const uint max = n-1;
  FixDeclBitTable( bt, BYTE_BIT, 0 );
  const uint nbits = lg_luint (max) + 1;
  const uint nbytes = ceil_quot(nbits, BYTE_BIT);
  uint x;

  do {
    randomize_sysCx (bt.s, nbytes);

    /* We can assume each bit is uniformly random,
     * so truncate as much as possible without excluding {max}.
     */
    x = get_uint_BitTable (bt, 0, nbits);

    /* If {x} is outside of our range, then try again.
     * This has less than a 50% chance of happening, so this loop will terminate eventually.
     */
  } while (x > max);

  return x;
}

