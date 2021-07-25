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
/* fileb.h - stdin_XFileB () */
/* fileb.h - stdout_OFileB () */
/* fileb.h - stderr_OFileB () */

#if defined(_MSC_VER)
#elif defined(__APPLE__)
#define LACE_POSIX_SOURCE
#else
#define LACE_POSIX_SOURCE
/* TODO: Figure out the correct POSIX_SOURCE to use!*/
#ifndef POSIX_SOURCE
#define POSIX_SOURCE
#endif
#ifndef _POSIX_SOURCE
#define _POSIX_SOURCE
#endif
#ifndef _POSIX_C_SOURCE
/* Needed by setenv().*/
#define _POSIX_C_SOURCE 200112L
#endif
#endif

#ifdef LACE_POSIX_SOURCE
#include <fcntl.h>
#include <unistd.h>
#include <sys/wait.h>
#else
#include <fcntl.h>
#include <windows.h>
#include <direct.h>
#include <io.h>
#include <process.h>
#ifdef _MSC_VER
typedef intptr_t pid_t;
#endif
#endif
#include <sys/stat.h>
#include <sys/types.h>
#include <stdio.h>

typedef int fd_t;

#include "def.h"

bool
closefd_sysCx (fd_t fd);
FILE*
fdopen_sysCx (fd_t fd, const char* mode);
bool
kill_please_sysCx(pid_t pid);

void
setenv_sysCx (const char* key, const char* val);
void
tacenv_sysCx (const char* key, const char* val);

bool
mkdir_sysCx (const char* pathname);
bool
rmdir_sysCx (const char* pathname);
bool
chdir_sysCx (const char* pathname);

#endif

