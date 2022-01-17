/**
 * \file syscx.c
 * Interact with the operating system.
 **/
#include "syscx.h"
#include "fildesh_compat_fd.h"
#include "fildesh_compat_sh.h"

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

  stderr_OFileB ();
  stdout_OFileB ();
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
  lose_OFileB(stdout_OFileB ());
  lose_OFileB(stderr_OFileB ());
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

    /* Flush these so the next message is last.*/
    flush_OFileB (stdout_OFileB ());
    flush_OFileB (stderr_OFileB ());

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

  void
dbglog_printf3 (const char* file,
    const char* func,
    uint line,
    const char* fmt,
    ...)
{
  va_list args;
  int err = errno;
  OFile* of = stderr_OFile ();

  while (true) {
    const char* tmp = strstr (file, "bld/");
    if (!tmp)  break;
    file = &tmp[4];
  }

  printf_OFile (of, "./%s(%u) %s: ", file, line, func);

  va_start (args, fmt);
  vprintf_OFile (of, fmt, args);
  va_end(args);

  oput_char_OFile (of, '\n');

  if (err != 0)
  {
#if 0
    /* Why no work? */
    const uint n = 2048 * sizeof(char);
    char* s;

    printf_FileB (of, "^^^ errno:%d ", err);

    s = (char*) ensure_OFile (of, n);
    s[0] = '\0';

    strerror_r (err, s, n);

    of->off += strlen (s) * sizeof(char);
    oput_char_File (of, '\n');
#else
    printf_OFile (of, "^^^ errno:%d %s\n", err, strerror (err));
#endif
    errno = 0;
  }
  flush_OFile (of);
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

  OFileB*
stdout_OFileB ()
{
  static bool initialized = false;
  static OFileB ofb[1];
  if (!initialized)
  {
    init_OFileB (ofb);
    ofb->fb.f = stdout;
    ofb->fb.fd = fileno_sysCx(stdout);
    initialized = true;
  }
  return ofb;
}

  OFileB*
stderr_OFileB ()
{
  static bool initialized = false;
  static OFileB ofb[1];
  if (!initialized)
  {
    init_OFileB (ofb);
    ofb->fb.f = stderr;
    ofb->fb.fd = fileno_sysCx(stderr);
    initialized = true;
  }
  return ofb;
}

  XFile*
stdin_XFile ()
{
  XFileB* xfb = stdin_XFileB ();
  return &xfb->xf;
}

  OFile*
stdout_OFile ()
{
  OFileB* ofb = stdout_OFileB ();
  return &ofb->of;
}

  OFile*
stderr_OFile ()
{
  OFileB* ofb = stderr_OFileB ();
  return &ofb->of;
}

  bool
closefd_sysCx (fd_t fd)
{
  if (fd == 0 && stdin_XFileB()->fb.f) {
    close_XFileB(stdin_XFileB());
    return true;
  } else if (fd == 1 && stdout_OFileB()->fb.f) {
    close_OFileB(stdout_OFileB());
    return true;
  } else if (fd == 2 && stderr_OFileB()->fb.f) {
    close_OFileB(stderr_OFileB());
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

/**
 * \param path  Return value. Can come in as a hint for the path name.
 **/
  void
mktmppath_sysCx (AlphaTab* path)
{
  const char* v = 0;
#ifdef LACE_POSIX_SOURCE
  pid_t pid = getpid ();
#else
  pid_t pid = _getpid ();
#endif
  OFile of[1] = {DEFAULT_OFile};
  zuint i;

#ifdef LACE_POSIX_SOURCE
  v = getenv ("TMPDIR");
  if (!v)  v = "/tmp";
#else
  v = getenv ("TEMP");
#endif

  if (!v)
  {
    path->sz = 0;
    return;
  }
  oput_cstr_OFile (of, v);
  oput_char_OFile (of, '/');
  oput_AlphaTab (of, path);
  oput_char_OFile (of, '-');
  oput_luint_OFile (of, pid);
  oput_char_OFile (of, '-');

  path->sz = 0;
  for (i = 0; i < SIZE_MAX; ++i) {
    zuint off = of->off;
    oput_luint_OFile (of, i);

    if (mkdir_sysCx (cstr1_OFile (of, 0))) {
      copy_AlphaTab_OFile (path, of);
      break;
    }

    of->off = off;
  }
  lose_OFile (of);
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
