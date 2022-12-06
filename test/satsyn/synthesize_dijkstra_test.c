#include "src/satsyn/instance.h"
#include "src/satsyn/synsearch.h"
#include <assert.h>

int main()
{
  XnSys sys = inst_dijkstra_XnSys(4);
  FMem_synsearch tape = cons1_FMem_synsearch(&sys);
  synsearch(&tape);
  assert(tape.stabilizing);
  lose_FMem_synsearch(&tape);
  lose_XnSys(&sys);
  return 0;
}

