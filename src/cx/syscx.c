/**
 * \file syscx.c
 * Interact with the operating system.
 **/
#include "syscx.h"

#include <errno.h>
#include <signal.h>
#include <stdlib.h>

# include <fcntl.h>
#ifndef _MSC_VER
# include <unistd.h>
# include <sys/wait.h>
#else
# include <windows.h>
# include <direct.h>
# include <io.h>
# include <process.h>
#endif
#include <sys/stat.h>
#include <sys/types.h>
#include <stdio.h>

#include <fildesh/fildesh_compat_fd.h>
#include <fildesh/fildesh_compat_sh.h>

#include "src/cx/table.h"

DeclTableT( HookFn, struct { void (*f) (); void* x; } );

static DeclTable( HookFn, LoseFns );
static const char* ExeName = 0;

  const char*
exename_of_sysCx ()
{
  return ExeName;
}

static
  void
signal_hook_sysCx (int sig)
{
  DBog1( "Caught signal: %d", sig );
  failout_sysCx ("");
}

/** Initialize the system.
 *
 * \return The number one.
 * \sa lose_sysCx()
 **/
  int
init_sysCx (int* pargc, char*** pargv)
{
  (void) pargc;
  ExeName = (*pargv)[0];

  signal (SIGSEGV, signal_hook_sysCx);
#ifdef _MSC_VER
  _setmode(_fileno(stdin), _O_BINARY);
  _setmode(_fileno(stdout), _O_BINARY);
  _setmode(_fileno(stderr), _O_BINARY);
#endif
  return 1;
}

  void
push_losefn_sysCx (void (*f) ())
{
  DeclGrow1Table( HookFn, hook, LoseFns );
  hook->f = f;
  hook->x = 0;
}
  void
push_losefn1_sysCx (void (*f) (void*), void* x)
{
  DeclGrow1Table( HookFn, hook, LoseFns );
  hook->f = (void (*) ()) f;
  hook->x = x;
}

  void
lose_sysCx ()
{
  static bool called = false;
  uint i;
  if (called) {
    assert(false);
    return;
  }
  UFor( i, LoseFns.sz ) {
    /* Do in reverse because it's a stack.*/
    DeclEltTable( HookFn, hook, LoseFns, LoseFns.sz-i-1 );
    if (hook->x)
      ((void (*) (void*)) hook->f) (hook->x);
    else
      hook->f ();
  }
  LoseTable( LoseFns );
  called = true;
}

  void
failout_sysCx (const char* msg)
{
  if (msg)
  {
    int err = errno;
    /* Use literal stderr just in case we have memory problems.*/
    FILE* f = stderr;

    fprintf (f, "FAILOUT: %s\n", exename_of_sysCx ());

#ifndef _MSC_VER
    {
      char hostname[128];
      uint n = ArraySz(hostname);
      gethostname(hostname, n);
      hostname[n-1] = 0;
      fprintf (f, "^^^ Host: %s\n", hostname);
    }
#endif

    if (msg[0])
      fprintf (f, "^^^ Reason: %s\n", msg);
    if (err != 0)
      fprintf (f, "^^^ errno:%d %s\n", err, strerror (err));
  }
  lose_sysCx ();
  if (false)
    abort();
  else
    exit(1);
}
