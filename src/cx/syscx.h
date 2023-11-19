/**
 * \file syscx.h
 **/
#ifndef sysCx_H_
#define sysCx_H_

static const char MagicArgv1_sysCx[] = "--opts://sysCx";

const char*
exename_of_sysCx ();
int
init_sysCx (int* pargc, char*** pargv);
void
push_losefn_sysCx (void (*f) ());
void
push_losefn1_sysCx (void (*f) (void*), void* x);
void
lose_sysCx ();

/* synhax.h - failout_sysCx() */
/* synhax.h - dbglog_printf3() */

#endif

