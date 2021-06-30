/*
 * \file ofile.h
 */
#ifndef OFile_H_
#define OFile_H_
#include "alphatab.h"
#include <stdarg.h>

typedef struct OFile OFile;
typedef struct OFileCtx OFileCtx;
typedef struct OFileVT OFileVT;

struct OFile
{
  TableT(byte) buf;
  zuint off;
  zuint flushsz;
  bool mayflush;
  const OFileVT* vt;
  OFileCtx* ctx;
};
#define DEFAULT3_OFile(flushsz, mayflush, vt) \
{ DEFAULT_Z_Table(byte), 0, flushsz, mayflush, vt, 0 }
#define DEFAULT_OFile  DEFAULT3_OFile(0, false, 0)

struct OFileCtx
{
  byte nothing;
};

struct OFileVT
{
  bool (*flush_fn) (OFile*);
  void (*close_fn) (OFile*);
  void (*free_fn) (OFile*);

  void (*oput_int_fn) (OFile*, int);
  void (*oput_uint_fn) (OFile*, uint);
  void (*oput_luint_fn) (OFile*, luint);
  void (*oput_real_fn) (OFile*, real);
  void (*oput_char_fn) (OFile*, char);
  void (*oput_AlphaTab_fn) (OFile*, const AlphaTab*);
  void (*vprintf_fn) (OFile*, const char*, va_list);
  void (*oputn_char_fn) (OFile*, const char*, zuint);
};
#define DEFAULT3_OFileVT(flush_fn, close_fn, free_fn) \
{ flush_fn, close_fn, free_fn, \
  0, 0, 0, 0, 0, 0, 0, 0 \
}


void
close_OFile (OFile* of);
void
lose_OFile (OFile* of);
void
free_OFile (OFile* of);
void
flush_OFile (OFile* of);
OFile*
null_OFile ();

void
oput_int_OFile (OFile* of, int x);
void
oput_uint_OFile (OFile* of, uint x);
void
oput_luint_OFile (OFile* of, luint x);
void
oput_ujint_OFile (OFile* of, ujint x);
void
oput_real_OFile (OFile* of, real x);
void
oput_char_OFile (OFile* of, char c);
void
oput_AlphaTab (OFile* of, const AlphaTab* t);
void
oput_OFile (OFile* of, OFile* src);
void
vprintf_OFile (OFile* of, const char* fmt, va_list args);
void
printf_OFile (OFile* of, const char* fmt, ...);
void
oputn_char_OFile (OFile* of, const char* a, zuint n);

/* Implemented in syscx.c */
OFile* stdout_OFile ();
OFile* stderr_OFile ();

qual_inline
  void
init_data_OFile (OFile* of)
{
  InitZTable( of->buf );
  of->off = 0;
  of->flushsz = 0;
  of->mayflush = false;
}

qual_inline
  OFile
dflt_OFile ()
{
  OFile of = DEFAULT_OFile;
  return of;
}

qual_inline
  void
init_OFile (OFile* of)
{
  *of = dflt_OFile ();
}

qual_inline
  Trit
mayflush_OFile (OFile* of, Trit may)
{
  bool old_mayflush = of->mayflush;
  if (may == Yes)  of->mayflush = true;

  if (of->mayflush && of->off >= of->flushsz)
    of->vt->flush_fn (of);

  if (may == Nil)  of->mayflush = false;
  return (old_mayflush ? Yes : Nil);
}

qual_inline
  void
oput_cstr_OFile (OFile* of, const char* s)
{
  const AlphaTab t = dflt1_AlphaTab (s);
  oput_AlphaTab (of, &t);
}

qual_inline
  const char*
ccstr1_of_OFile (const OFile* of, zuint off)
{ return (char*) &of->buf.s[off]; }

qual_inline
  const char*
ccstr_of_OFile (const OFile* of)
{ return ccstr1_of_OFile (of, of->off); }

qual_inline
  char*
cstr1_OFile (OFile* f, zuint off)
{ return (char*) &f->buf.s[off]; }

qual_inline
  char*
cstr_OFile (OFile* of)
{ return cstr1_OFile (of, of->off); }

qual_inline
  AlphaTab
AlphaTab_OFile (OFile* of, zuint off)
{
  AlphaTab t = DEFAULT_AlphaTab;
  t.s = (char*) &of->buf.s[off];
  t.sz = (of->off - off + 1) / sizeof(char);
  return t;
}

/** Get a window into the OFile content.
 * \param beg  Inclusive beginning index.
 * \param end  Non-inclusive end index.
 **/
qual_inline
  AlphaTab
window2_OFile (OFile* ofile, zuint beg, ujint end)
{
  AlphaTab t = DEFAULT_AlphaTab;
  Claim2( beg ,<=, end );
  Claim2( end ,<=, ofile->off );
  t.s = (char*) &ofile->buf.s[beg];
  t.sz = (end - beg) / sizeof(char);
  return t;
}

qual_inline
  void
cat_AlphaTab_OFile (AlphaTab* t, OFile* of)
{
  AlphaTab tmp = AlphaTab_OFile (of, 0);
  cat_AlphaTab (t, &tmp);
}

qual_inline
  void
copy_AlphaTab_OFile (AlphaTab* t, OFile* of)
{
  AlphaTab tmp = AlphaTab_OFile (of, 0);
  copy_AlphaTab (t, &tmp);
}

qual_inline
  void
init_AlphaTab_move_OFile (AlphaTab* t, OFile* of)
{
  *t = AlphaTab_OFile (of, 0);
  t->alloc_lgsz = of->buf.alloc_lgsz;
  init_data_OFile (of);
  PackTable( *t );
}

#endif

