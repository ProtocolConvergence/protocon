
#ifndef URandom_H_
#define URandom_H_
#include "def.h"

typedef struct URandom URandom;
struct URandom {
  uint32 state[17];
  uint32 salt;
  /* uint sys_pcidx; */
  /* uint sys_npcs; */
};

void
init2_seeded_URandom (URandom* urandom, uint pcidx, uint npcs);
void
init3_URandom (URandom* urandom, uint pcidx, uint npcs, uint seed);
void
init1_URandom (URandom* urandom, uint seed);
void
init2_URandom (URandom* urandom, uint pcidx, uint npcs);
uint32
uint32_URandom (URandom* urandom);
Bit
bit_URandom (URandom* urandom);
uint
uint_URandom (URandom* urandom, uint n);
void
shuffle_uints_URandom (URandom* urandom, uint* a, uint n);

uint
randommod_sysCx(uint n);
/* Implemented in syscx.c */
Bool
randomize_sysCx(void* p, uint size);

qual_inline
  void
init_URandom (URandom* urandom)
{ init2_URandom (urandom, 0, 1); }

/** Generate a real in [0,1).**/
qual_inline
  real
real_URandom (URandom* urandom)
{
  return (real) (uint32_URandom (urandom) * 2.328306e-10);
}

qual_inline
  bool
bool_URandom (URandom* urandom)
{ return (1 == bit_URandom (urandom)); }


#endif


