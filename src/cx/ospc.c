/**
 * \file ospc.c
 * Spawn and communicate with a process.
 **/
#include "ospc.h"
#include "lace_compat_fd.h"

  bool
close_OSPc (OSPc* ospc)
{
  bool good = false;
  if (ospc->pid < 0)  return 0;
  ospc->xf = NULL;
  ospc->of = NULL;
  close_XFileB (&ospc->xfb);
  close_OFileB (&ospc->ofb);
  /* if (ospc->pid > 0)  kill (ospc->pid, SIGKILL); */
  good = waitpid_sysCx (ospc->pid, &ospc->status);
  ospc->pid = -1;
  return good;
}

  void
lose_OSPc (OSPc* ospc)
{
  uint i;
  close_OSPc (ospc);
  lose_XFileB (&ospc->xfb);
  lose_OFileB (&ospc->ofb);
  lose_AlphaTab (&ospc->cmd);
  for (i = 0; i < ospc->args.sz; ++i) {
    lose_AlphaTab (&ospc->args.s[i]);
  }
  LoseTable( ospc->args );
}

/** Make a pipe to process input.
 **/
  void
stdxpipe_OSPc (OSPc* ospc)
{
  Claim( !ospc->of );
  ospc->of = &ospc->ofb.of;
}

/** Make a pipe from process output.
 **/
  void
stdopipe_OSPc (OSPc* ospc)
{
  Claim( !ospc->xf );
  ospc->xf = &ospc->xfb.xf;
}

  bool
spawn_OSPc (OSPc* ospc)
{
  fd_t xfd[2] = { -1, -1 };
  fd_t ofd[2] = { -1, -1 };
  DeclLegit( good );
  DeclTable( cstr, argv );
  uint nfrees = 0;
  uint i;

  if (ospc->of) {
    DoLegit( "pipe()" ) {
      good = (0 == lace_compat_fd_pipe(&xfd[1], &xfd[0]));
    }
  }
  if (ospc->xf) {
    DoLegit( "pipe()" ) {
      good = (0 == lace_compat_fd_pipe(&ofd[1], &ofd[0]));
    }
  }

  if (good)
  {
    PushTable( argv, dup_cstr (exename_of_sysCx ()) );
    PushTable( argv, dup_cstr (MagicArgv1_sysCx) );
    PushTable( argv, dup_cstr ("-exec") );
    PushTable( argv, dup_cstr (cstr_AlphaTab (&ospc->cmd)) );

    if (ospc->of)
    {
      PushTable( argv, dup_cstr ("-stdxfd") );
      PushTable( argv, itoa_dup_cstr (xfd[0]) );
    }
    if (ospc->xf)
    {
      PushTable( argv, dup_cstr ("-stdofd") );
      PushTable( argv, itoa_dup_cstr (ofd[1]) );
    }
    PushTable( argv, dup_cstr ("--") );
    nfrees = argv.sz;

    for (i = 0; i < ospc->args.sz; ++i) {
      PushTable( argv, cstr_AlphaTab (&ospc->args.s[i]) );
    }

    PushTable( argv, 0 );
  }

  if (good) {
    if (ospc->of) {
      lace_compat_fd_inherit(xfd[0]);
    }
    if (ospc->xf) {
      lace_compat_fd_inherit(ofd[1]);
    }
  }

  DoLegitP( ospc->pid >= 0, "spawn" )
    ospc->pid = spawnvp_sysCx (argv.s);

  DoLegit( 0 )
  {
    /* The old switcharoo. Your input is my output and vice-versa.*/
    if (ospc->of) {
      lace_compat_fd_close(xfd[0]);
      good = openfd_FileB(&ospc->ofb.fb, xfd[1]);
    }
    if (ospc->xf) {
     lace_compat_fd_close(ofd[1]);
      good = openfd_FileB(&ospc->xfb.fb, ofd[0]);
    }
  }

  for (i = 0; i < nfrees; ++i) {
    free (argv.s[i]);
  }
  LoseTable( argv );

  return good;
}

