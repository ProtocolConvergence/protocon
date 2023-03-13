
#ifndef FileB_H_
#define FileB_H_

#include "syscx.h"
#include "xfile.h"

#include <stdarg.h>
#include <stdio.h>

extern const XFileVT FileB_XFileVT;

typedef struct FileB FileB;
typedef struct XFileB XFileB;

enum FileB_Format {
  FileB_Ascii,
  FileB_Raw,
  FileB_NFormats
};
typedef enum FileB_Format FileB_Format;

struct FileB {
  FILE* f;
  fd_t fd;
  bool good;
  bool sink;
  bool byline;
  FileB_Format fmt;
  AlphaTab pathname;
  AlphaTab filename;
};
#define DEFAULT1_FileB(sink) \
{ \
  0, -1, true, \
  sink, false, FileB_Ascii, \
  DEFAULT_AlphaTab, DEFAULT_AlphaTab \
}

struct XFileB
{
  XFile xf;
  FileB fb;
};
#define DEFAULT_XFileB \
{ \
  DEFAULT3_XFile(BUFSIZ, true, &FileB_XFileVT), \
  DEFAULT1_FileB(false) \
}

void
init_XFileB (XFileB* xfb);

void
close_XFileB (XFileB* f);
void
lose_XFileB (XFileB* xfb);

byte*
ensure_XFileB (XFileB* xfb, zuint n);
void
setfmt_XFileB (XFileB* xfb, FileB_Format fmt);
void
dirname_AlphaTab (AlphaTab* dirname, const AlphaTab* path);
uint
pathname2_AlphaTab (AlphaTab* pathname, const char* opt_dir, const char* filename);
bool
open_FileB (FileB* f, const char* pathname, const char* filename);
bool
openfd_FileB (FileB* fb, fd_t fd);
void
set_FILE_FileB (FileB* fb, FILE* file);
char*
xget_XFileB (XFileB* xfb);

void
flush_XFileB (XFileB* xfb);


bool
xgetn_byte_XFileB (XFileB* xfb, byte* a, zuint n);

AlphaTab
textfile_AlphaTab (const char* pathname, const char* filename);

qual_inline
  bool
nullt_FileB (const FileB* f)
{
  return (f->fmt < FileB_Raw);
}

qual_inline
  bool
byline_FileB (const FileB* f)
{
  return f->byline;
}


/* Implemented in syscx.c */
XFileB* stdin_XFileB ();



#endif

