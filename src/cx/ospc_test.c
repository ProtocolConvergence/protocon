/**
 * \file ospc_test.c
 * Tests for processes.
 **/

#include "syscx.h"

#include "ospc.h"


  void
testfn_OSPc ()
{
  bool good = true;
  const char* s;
  OSPc ospc[] = {DEFAULT_OSPc};
  /* stdxpipe_OSPc (ospc); */
  stdopipe_OSPc (ospc);
  ospc->cmd = cons1_AlphaTab (exename_of_sysCx ());
  PushTable( ospc->args, cons1_AlphaTab ("echo") );
  PushTable( ospc->args, cons1_AlphaTab ("hello") );
  PushTable( ospc->args, cons1_AlphaTab ("world") );
  good = spawn_OSPc (ospc);
  Claim( good );
  /* close_OFileB (ospc->of); */
  xget_XFile (ospc->xf);
  s = cstr_XFile (ospc->xf);
  DBog1( "got: %s", s );
  Claim( eql_cstr (s, "hello world\n") );
  good = close_OSPc (ospc);
  Claim( good );
  lose_OSPc (ospc);
}


static
  void
testfn_exec ()
{
  pid_t pid = -1;
  int status = 1;
  const char* argv[4];
  bool good = false;
  argv[0] = exename_of_sysCx ();
  argv[1] = "wait0";
  argv[2] = "5"; /* Special exit code. */
  argv[3] = 0;

  fputs ("V spawn() called V\n", stderr);
  fflush (stderr);
  pid = spawnvp_sysCx ((char**) argv);

  good = waitpid_sysCx (pid, &status);
  fputs ("^ wait() returned ^\n", stderr);
  fflush (stderr);
  Claim( good );
  Claim2( status ,==, atoi (argv[2]) );
}


int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);

  /* Special test as child process. */
  if (eql_cstr (argv[argi], "echo")) {
    OFile* of = stdout_OFile ();
    for (argi += 1; argi < argc; ++argi) {
      oput_cstr_OFile (of, argv[argi]);
      oput_char_OFile (of, (argi + 1 < argc) ? ' ' : '\n');
    }
    lose_sysCx ();
    return 0;
  }
  if (eql_cstr (argv[argi], "wait0")) {
    argv[argi] = dup_cstr ("wait1");
    fputs (" V exec() called V\n", stderr);
    execvp_sysCx (argv);
    fputs (" ^ exec() failed? ^\n", stderr);
    return 1;
  }
  if (eql_cstr (argv[argi], "wait1")) {
    /* _sleep (1); */
    /* sleep (1); */
    fputs ("  V exec()'d process exits V\n", stderr);
    return atoi (argv[argi+1]);
  }

  testfn_OSPc();
  testfn_exec();

  lose_sysCx ();
  return 0;
}
