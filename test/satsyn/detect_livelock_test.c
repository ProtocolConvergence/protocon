
#include "src/satsyn/detect.h"
#include <assert.h>

/**
 * Test that detect_livelock() works.
 * \sa detect_livelock()
 **/
int main()
{
  BitTable legit = cons2_BitTable (6, 0);
  DeclTable( Xns, xns );
  FMem_detect_livelock mem_detect_livelock;
  bool livelock_exists;

  GrowTable( xns, legit.sz );
  for (unsigned i = 0; i < xns.sz; ++i) {
    InitTable( xns.s[i] );
  }

  mem_detect_livelock = cons1_FMem_detect_livelock(&legit);


  PushTable( xns.s[0], 1 );
  livelock_exists = detect_livelock(&mem_detect_livelock, xns);
  assert(!livelock_exists);

  PushTable( xns.s[1], 5 );
  PushTable( xns.s[1], 3 );
  PushTable( xns.s[2], 1 );
  PushTable( xns.s[3], 4 );
  PushTable( xns.s[4], 2 );

  livelock_exists = detect_livelock(&mem_detect_livelock, xns);
  assert(livelock_exists);

  lose_FMem_detect_livelock(&mem_detect_livelock);

  for (unsigned i = 0; i < xns.sz; ++i) {
    LoseTable( xns.s[i] );
  }
  LoseTable( xns );
  lose_BitTable (&legit);
  return 0;
}

