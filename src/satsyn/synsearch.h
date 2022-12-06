#ifndef SATSYN_SYNSEARCH_H_
#define SATSYN_SYNSEARCH_H_

#if defined(__cplusplus)
extern "C" {
#endif

#include "detect.h"

typedef struct FMem_do_XnSys FMem_do_XnSys;
typedef struct FMem_synsearch FMem_synsearch;

struct FMem_do_XnSys
{
    XnDomSz* vals;
    BitTable fixed;
    TableT(XnEVbl) evs;
    const XnSys* sys;
};

struct FMem_synsearch
{
    bool stabilizing;
    const XnSys* sys;
    FMem_detect_livelock livelock_tape;
    FMem_detect_convergence convergence_tape;
    FMem_do_XnSys dostates_tape;
    TableT(Xns) xns;
    TableT(XnSz) xn_stk;
    TableT(XnRule) rules;
    TableT(Xns) may_rules;
    TableT(XnSz) cmp_xn_stk;
    TableT(XnSz2) influence_order;
    uint n_cached_rules;
    uint n_cached_may_rules;
    uint rule_nwvbls;
    uint rule_nrvbls;
    TableT(XnSz) legit_states;
    TableT(Xns) legit_xns;
};

FMem_do_XnSys
cons1_FMem_do_XnSys(const XnSys* sys);
void
lose_FMem_do_XnSys(FMem_do_XnSys* tape);
FMem_synsearch
cons1_FMem_synsearch(const XnSys* sys);
void
lose_FMem_synsearch(FMem_synsearch* tape);

void
do_XnSys(FMem_do_XnSys* tape, BitTable bt);

void
do_push_XnSys(FMem_do_XnSys* tape, TableT(XnSz)* t);
Trit
detect_strong_convergence(FMem_synsearch* tape);

void
back1_Xn(TableT(Xns)* xns, TableT(XnSz)* stk);


XnSz
apply1_XnRule(const XnRule* g, const XnSys* sys, XnSz sidx);

void
add_XnRule(FMem_synsearch* tape, const XnRule* g);

void
set_may_rules(FMem_synsearch* tape, TableT(XnSz)* may_rules, XnRule* g);

XnRule*
grow1_rules_synsearch(FMem_synsearch* tape);

TableT(XnSz)*
grow1_may_rules_synsearch(FMem_synsearch* tape);

void
synsearch_quicktrim_mayrules(FMem_synsearch* tape, XnSz nadded);
void
synsearch_trim(FMem_synsearch* tape);

bool
synsearch_check_weak (FMem_synsearch* tape, XnSz* ret_nreqrules);
void
synsearch(FMem_synsearch* tape);

#if defined(__cplusplus)
}
#endif
#endif  /* #ifndef SATSYN_SYNSEARCH_H_ */
