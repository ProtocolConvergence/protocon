#ifndef SATSYN_DETECT_H_
#define SATSYN_DETECT_H_

#if defined(__cplusplus)
extern "C" {
#endif

#include "xnsys.h"

typedef struct FMem_detect_livelock FMem_detect_livelock;
typedef struct FMem_detect_convergence FMem_detect_convergence;
struct FMem_detect_livelock
{
    BitTable cycle;
    BitTable tested;
    TableT(XnSz2) testing;
    const BitTable* legit;
};

struct FMem_detect_convergence
{
    const BitTable* legit;
    TableT(Xns) bxns;
    TableT(XnSz) reach;
    BitTable tested;
};

FMem_detect_livelock
cons1_FMem_detect_livelock (const BitTable* legit);
void
lose_FMem_detect_livelock (FMem_detect_livelock* tape);

FMem_detect_convergence
cons1_FMem_detect_convergence (const BitTable* legit);
void
lose_FMem_detect_convergence (FMem_detect_convergence* tape);

bool
detect_livelock(FMem_detect_livelock* tape,
                const TableT(Xns) xns);
bool
detect_convergence(FMem_detect_convergence* tape,
                   const TableT(Xns) xns);

#if defined(__cplusplus)
}
#endif
#endif  /* #ifndef SATSYN_DETECT_H_ */
