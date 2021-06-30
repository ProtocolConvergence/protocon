
#include "ofile.h"
#include <stdio.h>

  void
close_OFile (OFile* of)
{
  VTCall( of->vt, (void),close_fn,(of) );
}

  void
lose_OFile (OFile* of)
{
  LoseTable( of->buf );
}

  void
free_OFile (OFile* of)
{
  VTCall( of->vt, (void),free_fn,(of) );
}

  void
flush_OFile (OFile* of)
{
  /* In the future, we may not want to flush all the time!*/
  /* Also, we may not wish to flush the whole buffer.*/
  VTCall( of->vt, (void),flush_fn,(of); return );

  Claim2( of->flushsz ,==, 0 );
  if (of->off > 0)
  {
    of->off = 0;
    of->buf.sz = 1;
    of->buf.s[0] = 0;
  }
}

static void do_nothing_OFile () {}
static bool do_nothing_true_OFile () {return true;}

  OFile*
null_OFile ()
{
  static bool vt_initialized = false;
  static OFileVT vt;
  static OFile of[1];

  if (!vt_initialized) {
    void (*f) () = do_nothing_OFile;
    memset (&vt, 0, sizeof (vt));
    vt.flush_fn = (bool (*) (OFile*)) do_nothing_true_OFile;
    vt.free_fn = (void (*) (OFile*)) f;
    vt.close_fn = (void (*) (OFile*)) f;
    vt.oput_int_fn = (void (*) (OFile*, int)) f;
    vt.oput_uint_fn = (void (*) (OFile*, uint)) f;
    vt.oput_luint_fn = (void (*) (OFile*, luint)) f;
    vt.oput_real_fn = (void (*) (OFile*, real)) f;
    vt.oput_char_fn = (void (*) (OFile*, char)) f;
    vt.oput_AlphaTab_fn = (void (*) (OFile*, const AlphaTab*)) f;
    vt.vprintf_fn = (void (*) (OFile*, const char*, va_list)) f;
    vt.oputn_char_fn = (void (*) (OFile*, const char*, zuint)) f;

    vt_initialized = true;

    init_OFile (of);
    of->vt = &vt;
  }
  return of;
}

  void
oput_int_OFile (OFile* f, int x)
{
  VTCall( f->vt, (void),oput_int_fn,(f, x); return );
  EnsizeTable( f->buf, f->off + 50 );
  f->off += sprintf (cstr_OFile (f), "%i", x);
  mayflush_OFile (f, May);
}

  void
oput_uint_OFile (OFile* f, uint x)
{
  VTCall( f->vt, (void),oput_uint_fn,(f, x); return );
  EnsizeTable( f->buf, f->off + 50 );
  f->off += sprintf (cstr_OFile (f), "%u", x);
  mayflush_OFile (f, May);
}

  void
oput_luint_OFile (OFile* f, luint x)
{
  VTCall( f->vt, (void),oput_luint_fn,(f, x); return );
  EnsizeTable( f->buf, f->off + 50 );
  f->off += sprintf (cstr_OFile (f), "%lu", x);
  mayflush_OFile (f, May);
}

void oput_ujint_OFile (OFile* f, ujint x) { oput_luint_OFile (f, x); }

  void
oput_real_OFile (OFile* f, real x)
{
  VTCall( f->vt, (void),oput_real_fn,(f, x); return );
  EnsizeTable( f->buf, f->off + 50 );
  f->off += sprintf (cstr_OFile (f), "%.16e", x);
  mayflush_OFile (f, May);
}

  void
oput_char_OFile (OFile* f, char c)
{
  VTCall( f->vt, (void),oput_char_fn,(f, c); return );
  EnsizeTable( f->buf, f->off + 2 );
  f->buf.s[f->off] = c;
  f->buf.s[++f->off] = 0;
  mayflush_OFile (f, May);
}

  void
oput_AlphaTab (OFile* of, const AlphaTab* t)
{
  zuint n = t->sz;
  VTCall( of->vt, (void),oput_AlphaTab_fn,(of, t); return );
  if (n == 0)  return;
  if (!t->s[n-1])  -- n;
  GrowTable( of->buf, n*sizeof(char) );
  memcpy (&of->buf.s[of->off], t->s, n*sizeof(char));
  of->buf.s[of->buf.sz-1] = 0;
  of->off += n;
  mayflush_OFile (of, May);
}

  void
oput_OFile (OFile* of, OFile* src)
{
  AlphaTab ab = AlphaTab_OFile (src, 0);
  oput_AlphaTab (of, &ab);
}

  void
vprintf_OFile (OFile* f, const char* fmt, va_list args)
{
  zuint sz = 2048;  /* Not good :( */
  int iret = 0;
  VTCall( f->vt, (void),vprintf_fn,(f, fmt, args); return );

  EnsizeTable( f->buf, f->off + sz );
  iret = vsprintf ((char*) &f->buf.s[f->off], fmt, args);
  Claim2( iret ,>=, 0 );
  Claim2( (uint) iret ,<=, sz );
  f->off += iret;
  mayflush_OFile (f, May);
}

  void
printf_OFile (OFile* f, const char* fmt, ...)
{
  va_list args;
  va_start (args, fmt);
  vprintf_OFile (f, fmt, args);
  va_end (args);
}

  void
oputn_char_OFile (OFile* of, const char* a, zuint n)
{
  VTCall( of->vt, (void),oputn_char_fn,(of, a, n); return );
  GrowTable( of->buf, n );
  memcpy (&of->buf.s[of->off], a, n*sizeof(char));
  of->off += n;
  of->buf.s[of->off] = 0;
  mayflush_OFile (of, May);
}

