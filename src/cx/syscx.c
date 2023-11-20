/**
 * \file syscx.c
 * Interact with the operating system.
 **/
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef _MSC_VER
# include <unistd.h>
#else
# include <fcntl.h>
# include <windows.h>
#endif

  void
failout_sysCx (const char* msg)
{
  if (msg)
  {
    int err = errno;
    /* Use literal stderr just in case we have memory problems.*/
    FILE* f = stderr;

    fputs("FAILOUT: protocon tool\n", f);

#ifndef _MSC_VER
    {
      char hostname[128];
      hostname[0] = '\0';
      gethostname(hostname, sizeof(hostname));
      hostname[sizeof(hostname)-1] = '\0';
      fprintf (f, "^^^ Host: %s\n", hostname);
    }
#endif

    if (msg[0])
      fprintf (f, "^^^ Reason: %s\n", msg);
    if (err != 0)
      fprintf (f, "^^^ errno:%d %s\n", err, strerror (err));
  }
  exit(1);
}
