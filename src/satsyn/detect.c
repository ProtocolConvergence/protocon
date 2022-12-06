
#include "detect.h"

  FMem_detect_livelock
cons1_FMem_detect_livelock(const BitTable* legit)
{
  FMem_detect_livelock tape;

  tape.legit = legit;

  tape.cycle = cons1_BitTable(legit->sz);
  tape.tested = cons1_BitTable(legit->sz);
  InitTable( tape.testing );
  return tape;
}

  void
lose_FMem_detect_livelock(FMem_detect_livelock* tape)
{
  lose_BitTable(&tape->cycle);
  lose_BitTable(&tape->tested);
  LoseTable( tape->testing );
}

  FMem_detect_convergence
cons1_FMem_detect_convergence(const BitTable* legit)
{
  XnSz n = legit->sz;
  FMem_detect_convergence tape;

  tape.legit = legit;

  InitTable( tape.bxns );
  EnsizeTable( tape.bxns, n );
  for (unsigned i = 0; i < n; ++i) {
    InitTable( tape.bxns.s[i] );
  }

  InitTable( tape.reach );
  tape.tested = cons1_BitTable(n);
  return tape;
}

  void
lose_FMem_detect_convergence(FMem_detect_convergence* tape)
{
  for (unsigned i = 0; i < tape->bxns.sz; ++i) {
    LoseTable( tape->bxns.s[i] );
  }
  LoseTable( tape->bxns );

  LoseTable( tape->reach );
  lose_BitTable(&tape->tested);
}

/**
 * Detect a livelock in the current set of transition rules.
 * This is just a cycle check.
 **/
  bool
detect_livelock(FMem_detect_livelock* tape,
                const TableT(Xns) xns)
{
  size_t testidx = 0;
  BitTable cycle = tape->cycle;
  BitTable tested = tape->tested;
  TableT(XnSz2) testing = tape->testing;

  if (xns.sz == 0)  return false;
  testing.sz = 0;

  op_BitTable(cycle, BitOp_IDEN1, *tape->legit);
  op_BitTable(tested, BitOp_IDEN1, *tape->legit);

  while (true)
  {
    XnSz i, j;
    XnSz2* top;

    if (testing.sz > 0)
    {
      top = TopTable( testing );
      i = top->i;
      j = top->j;
    }
    else
    {
      while (testidx < xns.sz &&
             test_BitTable (tested, testidx))
      {
        ++ testidx;
      }

      if (testidx == xns.sz)  break;

      top = Grow1Table( testing );
      top->i = i = testidx;
      top->j = j = 0;
      ++ testidx;

      set1_BitTable (cycle, i);
    }

    while (j < xns.s[i].sz)
    {
      size_t k = xns.s[i].s[j];

      ++j;

      if (!test_BitTable (tested, k))
      {
        if (set1_BitTable (cycle, k))
        {
          tape->testing = testing;
          return true;
        }

        top->i = i;
        top->j = j;
        top = Grow1Table( testing );
        top->i = i = k;
        top->j = j = 0;
      }
    }

    if (j == xns.s[i].sz)
    {
      set1_BitTable (tested, i);
      -- testing.sz;
    }
  }
  tape->testing = testing;
  return false;
}


/**
 * Check to see that, for any state, there exists a path to a legit state.
 * Assume the set of legit states is closed under all transitions.
 **/
  bool
detect_convergence(FMem_detect_convergence* tape,
                   const TableT(Xns) xns)
{
  TableT(Xns) bxns = tape->bxns;
  TableT(XnSz) reach = tape->reach;
  BitTable tested = tape->tested;
  XnSz nreached = 0;

  for (unsigned i = 0; i < bxns.sz; ++i) {
    bxns.s[i].sz = 0;
  }
  reach.sz = 0;

  op_BitTable(tested, BitOp_IDEN1, *tape->legit);

  for (unsigned i = 0; i < xns.sz; ++i) {
    if (test_BitTable (tested, i))
    {
      ++ nreached;
      PushTable( reach, i );
    }

    for (unsigned j = 0; j < xns.s[i].sz; ++j) {
      PushTable( bxns.s[xns.s[i].s[j]], i );
    }
  }

  while (reach.sz > 0)
  {
    XnSz i = *TopTable( reach );
    -- reach.sz;
    for (unsigned j = 0; j < bxns.s[i].sz; ++j) {
      XnSz k = bxns.s[i].s[j];
      if (!set1_BitTable (tested, k))
      {
        ++ nreached;
        PushTable( reach, k );
      }
    }
  }

  tape->bxns = bxns;
  tape->reach = reach;
  return (nreached == tested.sz);
}

