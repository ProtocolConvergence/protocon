
#include "synhax.hh"

#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

  void
dbglog_printf3 (const char* file,
                const char* func,
                uint line,
                const char* fmt,
                ...)
{
  va_list args;
  int err = errno;
  FILE* f = stderr;

  fprintf(f, "%s(%u) %s: ", file, line, func);

  va_start(args, fmt);
  vfprintf(f, fmt, args);
  va_end(args);

  fputc('\n', f);

  if (err != 0) {
    fprintf(f, "^^^ errno:%d %s\n", err, strerror(err));
    errno = 0;
  }
  fflush(f);
}
