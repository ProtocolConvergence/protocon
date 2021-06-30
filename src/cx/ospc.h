
#ifndef OSPc_H_
#define OSPc_H_
#include "syscx.h"
#include "fileb.h"

typedef struct OSPc OSPc;

/**
 *               _
 *              | |
 *  this-proc o x |
 *            |   |
 *     ospc   x o |
 *              |_|
 *
 * The /xf/ and /of/ in OSPc are the 'o' and 'x' of /this-proc/ respectively.
 **/
struct OSPc
{
  AlphaTab cmd;
  TableT(AlphaTab) args;
  OFile* of; /**< Write to process (its stdin).**/
  XFile* xf; /**< Read from process (its stdout).**/
  pid_t pid;
  OFileB ofb;
  XFileB xfb;
  int status;
};
#define DEFAULT_OSPc \
{ DEFAULT_AlphaTab, \
  DEFAULT_Table, \
  0, 0, \
  -1, \
  DEFAULT_OFileB, \
  DEFAULT_XFileB, \
  0 \
}

qual_inline
  OSPc
dflt_OSPc ()
{
  OSPc p = DEFAULT_OSPc;
  return p;
}

qual_inline
void init_OSPc (OSPc* ospc) { *ospc = dflt_OSPc (); }

bool
close_OSPc (OSPc* ospc);
void
lose_OSPc (OSPc* ospc);
void
stdxpipe_OSPc (OSPc* ospc);
void
stdopipe_OSPc (OSPc* ospc);
bool
spawn_OSPc (OSPc* ospc);

#endif

