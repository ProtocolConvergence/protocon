#ifndef SATSYN_PROMELA_H_
#define SATSYN_PROMELA_H_

#if defined(__cplusplus)
extern "C" {
#endif
#include "xnsys.h"

void
oput_promela_state_XnSys (OFile* of, const XnSys* sys, XnSz sidx);
void
oput_promela_XnRule (OFile* of, const XnRule* g, const XnSys* sys);
void
oput_promela (OFile* of, const XnSys* sys, const TableT(XnRule) rules);

#if defined(__cplusplus)
}
#endif
#endif  /* #ifndef SATSYN_PROMELA_H_ */
