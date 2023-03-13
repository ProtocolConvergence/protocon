/**
 * \file syscx.c
 * Interact with the operating system.
 **/
#include "syscx.h"
#include <fildesh/fildesh_compat_fd.h>
#include <fildesh/fildesh_compat_sh.h>

#include "fileb.h"

#include <errno.h>
#include <signal.h>

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

  stdin_XFileB ();
  signal (SIGSEGV, signal_hook_sysCx);
#ifndef LACE_POSIX_SOURCE
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

  lose_XFileB(stdin_XFileB ());
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

#ifdef LACE_POSIX_SOURCE
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

static int fileno_sysCx(FILE* file) {
#ifdef _MSC_VER
  return _fileno(file);
#else
  return fileno(file);
#endif
}

  XFileB*
stdin_XFileB ()
{
  static bool initialized = false;
  static XFileB xfb[1];
  if (!initialized) {
    init_XFileB (xfb);
    xfb->fb.f = stdin;
    xfb->fb.fd = fileno_sysCx(stdin);
    xfb->fb.byline = true;
    initialized = true;
  }
  return xfb;
}

  XFile*
stdin_XFile ()
{
  XFileB* xfb = stdin_XFileB ();
  return &xfb->xf;
}

  bool
closefd_sysCx (fd_t fd)
{
  if (fd == 0 && stdin_XFileB()->fb.f) {
    close_XFileB(stdin_XFileB());
    return true;
  }
  return (0 == fildesh_compat_fd_close(fd));
}

  FILE*
fdopen_sysCx (fd_t fd, const char* mode)
{
#ifdef LACE_POSIX_SOURCE
  return fdopen (fd, mode);
#else
  return _fdopen (fd, mode);
#endif
}

  bool
kill_please_sysCx(pid_t pid)
{
#ifdef LACE_POSIX_SOURCE
  return (0 == kill(pid, SIGINT));
#else
  bool success = false;
  HANDLE handle = OpenProcess(PROCESS_TERMINATE, false, pid);
  if (handle) {
    success = !!TerminateProcess(handle, 1);
    CloseHandle(handle);
  }
  return success;
#endif
}

  void
setenv_sysCx (const char* key, const char* val)
{
#ifdef LACE_POSIX_SOURCE
  setenv (key, val, 1);
#else
  SetEnvironmentVariable (key, val);
  /* DBog2( "key:%s val:%s", key, val ); */
#endif
}

  void
tacenv_sysCx (const char* key, const char* val)
{
#ifdef LACE_POSIX_SOURCE
  const char* sep = ":";
#else
  const char* sep = ";";
#endif
  char* v;
  DecloStack1( AlphaTab, dec, cons1_AlphaTab (val) );

  v = getenv (key);
  if (v)
  {
    cat_cstr_AlphaTab (dec, sep);
    cat_cstr_AlphaTab (dec, v);
  }

  setenv_sysCx (key, cstr_AlphaTab (dec));
  lose_AlphaTab (dec);
}

  bool
mkdir_sysCx (const char* pathname)
{
  int ret = -1;
#ifdef LACE_POSIX_SOURCE
  ret = mkdir (pathname, 0700);
#else
  ret = _mkdir (pathname);
#endif
  return (ret == 0);
}

  bool
rmdir_sysCx (const char* pathname)
{
  int ret = -1;
#ifdef LACE_POSIX_SOURCE
  ret = rmdir (pathname);
#else
  ret = _rmdir (pathname);
#endif
  return (ret == 0);
}

  bool
chdir_sysCx (const char* pathname)
{
  int ret = -1;
#ifdef LACE_POSIX_SOURCE
  ret = chdir (pathname);
#else
  ret = _chdir (pathname);
#endif
  return (ret == 0);
}
