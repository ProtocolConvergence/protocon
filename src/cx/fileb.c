/**
 * \file fileb.c
 * Simple and advanced file I/O and parsing.
 **/
#include "fileb.h"
#include <fildesh/fildesh_compat_fd.h>

#include <assert.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>

static bool
xget_chunk_XFileB (XFileB* xfb);
static bool
xget_chunk_fn_XFileB (XFile* xf);

static void
close_fn_XFileB (XFile* xf);
static void
free_fn_XFileB (XFile* xf);

const XFileVT FileB_XFileVT = DEFAULT3_XFileVT(xget_chunk_fn_XFileB, close_fn_XFileB, free_fn_XFileB);

static
  void
init_FileB (FileB* fb, bool sink)
{
  fb->f = 0;
  fb->fd = -1;
  fb->good = true;
  fb->sink = sink;
  fb->byline = false;
  fb->fmt = FileB_Ascii;
  fb->pathname = dflt_AlphaTab ();
  fb->filename = dflt_AlphaTab ();
}

  void
init_XFileB (XFileB* xfb)
{
  static XFileCtx ctx;
  init_XFile (&xfb->xf);
  xfb->xf.flushsz = BUFSIZ;
  xfb->xf.mayflush = true;
  init_FileB (&xfb->fb, false);
  xfb->xf.vt = &FileB_XFileVT;
  xfb->xf.ctx = &ctx;
}

static
  void
close_FileB (FileB* f)
{
  if (f->f) {
    assert(f->fd >= 0);
    fclose (f->f);
    f->f = NULL;
    f->fd = -1;
  }
  assert(f->fd < 0);
}

  void
close_XFileB (XFileB* f)
{
  close_FileB (&f->fb);
  f->xf.off = 0;
  LoseTable(f->xf.buf);
  InitTable(f->xf.buf);
}

  void
close_fn_XFileB (XFile* xf)
{
  close_XFileB (CastUp( XFileB, xf, xf ));
}

  void
lose_XFileB (XFileB* xfb)
{
  close_XFileB (xfb);
  LoseTable( xfb->xf.buf );
  lose_AlphaTab (&xfb->fb.pathname);
  lose_AlphaTab (&xfb->fb.filename);
}

  void
free_fn_XFileB (XFile* xf)
{
  XFileB* xfb = CastUp( XFileB, xf, xf );
  lose_XFileB (xfb);
  free (xfb);
}

static inline
  zuint
chunksz_XFileB (XFileB* xfb)
{
  (void) xfb;
  return BUFSIZ;
}

  byte*
ensure_XFileB (XFileB* xfb, zuint n)
{
  XFile* const xf = &xfb->xf;
  zuint sz = xf->buf.sz;
  if (nullt_FileB (&xfb->fb))
  {
    Claim2( 0 ,<, sz );
    sz -= 1;
  }
  GrowTable( xf->buf, n );
  return &xf->buf.s[sz];
}

  void
setfmt_XFileB (XFileB* xfb, FileB_Format fmt)
{
  XFile* const xf = &xfb->xf;
  bool nullt0, nullt1;

  nullt0 = nullt_FileB (&xfb->fb);
  xfb->fb.fmt = fmt;
  nullt1 = nullt_FileB (&xfb->fb);
  if (nullt0 && !nullt1) {
    xf->buf.sz -= 1;
  }
}

static
  uint
dirname_sz (const char* path)
{
  const char* prev;
  const char* s;

  if (!path)  return 0;

  prev = path;
  s = strchr (path, '/');
  while (s) {
    prev = &s[1];
    s = strchr (prev, '/');
  }

  return IdxElt( path, prev );
}

static
  bool
absolute_path (const char* path)
{
  return path[0] == '/';
}

  void
dirname_AlphaTab (AlphaTab* dirname, const AlphaTab* path)
{
  const uint pflen = dirname_sz (ccstr_of_AlphaTab (path));
  const Bool add_rel =
    ((pflen == 0)
     || (path->s[0] != '/' && path->s[0] != '.'));

  if (dirname != path) {
    if (add_rel)
      copy_cstr_AlphaTab (dirname, "./");
    else
      flush_AlphaTab (dirname);
    cat1_cstr_AlphaTab (dirname, path->s, pflen);
  }
  else {
    dirname->s[pflen] = '\0';
    dirname->sz = pflen+1;
    if (add_rel)
      tac_cstr_AlphaTab (dirname, "./");
  }
}

/** Construct a path relative to a directory.
 *
 * \param pathname  Return value.
 * \param opt_dir  Optional directory name that the file is relative to.
 * \param file  Relative or absolute path to a file/directory.
 *
 * \sa assign2_AlphaTab()
 *
 * \return Index where the file basename starts.
 **/
  uint
pathname2_AlphaTab (AlphaTab* pathname, const char* opt_dir, const char* filename)
{
  char* s = strrchr (filename, '/');
  const uint pflen = (s ? IdxElt( filename, s ) + 1 : 0);
  const uint flen = strlen (filename) - pflen;
  uint plen = (opt_dir ? strlen (opt_dir) : 0);

  if (pflen > 0 && absolute_path (filename))
    plen = 0;

  if (plen > 0 && opt_dir[plen-1] != '/')
    plen += 1;

  ResizeTable( *pathname, plen+pflen+flen+1 );

  s = pathname->s;
  if (plen > 0)
  {
    memcpy (s, opt_dir, (plen-1)*sizeof(char));
    s[plen-1] = '/';
    s = &s[plen];
  }
  memcpy (s, filename, (pflen+flen+1)*sizeof(char));

  plen += pflen;
  return plen;
}

  bool
open_FileB (FileB* f, const char* pathname, const char* filename)
{
  static const char dev_fd_prefix[] = "/dev/fd/";
  uint sepidx = pathname2_AlphaTab (&f->pathname, pathname, filename);

  if (pfxeq_cstr(dev_fd_prefix, f->pathname.s)) {
    int fd = -1;
    xget_int_cstr(&fd, &f->pathname.s[strlen(dev_fd_prefix)]);
    if (fd >= 0) {
      openfd_FileB(f, fd);
    }
  } else {
    FILE* file = fopen (f->pathname.s, (f->sink ? "wb" : "rb"));
    if (file) {
      set_FILE_FileB(f, file);
    }
  }

  assign2_AlphaTab (&f->filename, &f->pathname, sepidx, f->pathname.sz);
  assign2_AlphaTab (&f->pathname, &f->pathname, 0, sepidx);

  return !!f->f;
}

  bool
openfd_FileB (FileB* fb, fd_t fd)
{
  assert(fd >= 0);
  assert(!fb->f);
  assert(fb->fd < 0);

  fb->fd = fildesh_compat_fd_claim(fd);
  fb->f = fdopen_sysCx (fd, (fb->sink ? "wb" : "rb"));
  return !!fb->f;
}

  void
set_FILE_FileB (FileB* fb, FILE* file)
{
  assert(file);
  assert(!fb->f);
  assert(fb->fd < 0);
  fb->f = file;
#ifdef _MSC_VER
  fb->fd = _fileno(file);
#else
  fb->fd = fileno(file);
#endif
}

  char*
xget_XFileB (XFileB* xfb)
{
  XFile* const xf = &xfb->xf;
  DeclLegit( good );
  long ret = -1;

  DoLegitLine( "" )
    !!xfb->fb.f;
#ifndef _MSC_VER
  DoLegit( 0 )
    ret = fseek (xfb->fb.f, 0, SEEK_END);
#endif

  /* Some streams cannot be seeked.*/
  if (good && ret != 0)
  {
    errno = 0; /* Not an error.*/
    xget_XFile (xf);
  }
  else
  {
    size_t sz = 0;

    DoLegitP( ret >= 0, "ftell()" )
      ret = ftell (xfb->fb.f);

    DoLegitP( ret == 0, "fseek()" ) {
      sz = ret;
      ret = fseek (xfb->fb.f, 0, SEEK_SET);
    }

    DoLegitP( ret == (long)sz, "fread()" )
    {
      GrowTable( xf->buf, sz );

      /* Note this relation!*/
      Claim2( xf->off + sz ,==, xf->buf.sz-1 );

      ret = fread (&xf->buf.s[xf->off], 1, sz, xfb->fb.f);
      if (ret >= 0)
        xf->buf.s[xf->off + ret] = '\0';
    }
  }

  if (good)
  {
    char* s = cstr_XFile (xf);
    xf->off = xf->buf.sz-1;
    return s;
  }
  return NULL;
}

  bool
xget_chunk_XFileB (XFileB* xfb)
{
  const zuint chunksz = chunksz_XFileB (xfb);
  TableT(byte)* buf = &xfb->xf.buf;
  size_t n;
  byte* s;

  if (!xfb->fb.f)  return false;

  s = ensure_XFileB (xfb, chunksz);

  if (byline_FileB (&xfb->fb))
  {
    char* line = (char*) s;
    Claim( nullt_FileB (&xfb->fb) );
    /* Don't worry about actually reading a full line here,
     * that's at a higher level.
     * We just want to avoid deadlock by stopping at a newline.
     */
    line = fgets (line, chunksz, xfb->fb.f);
    n = (line ? strlen (line) : 0);
  }
  else
  {
    n = fread (s, 1, chunksz, xfb->fb.f);
  }
  if (nullt_FileB (&xfb->fb))
    s[n] = 0;
  buf->sz -= (chunksz - n);
  return (n != 0);
}

  bool
xget_chunk_fn_XFileB (XFile* xf)
{
  return xget_chunk_XFileB (CastUp( XFileB, xf, xf ));
}

  void
flush_XFileB (XFileB* xfb)
{
  XFile* const f = &xfb->xf;
  TableT(byte)* buf = &f->buf;
  if (nullt_FileB (&xfb->fb))
  {
    Claim2( 0 ,<, buf->sz );
    Claim2( 0 ,==, buf->s[buf->sz-1] );
    Claim2( f->off ,<, buf->sz );
  }
  else
  {
    Claim2( f->off ,<=, buf->sz );
  }
  if (f->off == 0)  return;
  buf->sz = buf->sz - f->off;
  if (buf->sz > 0)
  {
    memmove (buf->s, &buf->s[f->off], buf->sz);
  }
  else if (nullt_FileB (&xfb->fb))
  {
    Claim(0);
    /* TODO - When does this even happen?*/
    buf->s[0] = 0;
    buf->sz = 1;
  }
  f->off = 0;
}

  bool
xget_uint_XFileB (XFileB* xfb, uint* x)
{
  XFile* const xf = &xfb->xf;
  const char* s;
  if (!xfb->fb.good)  return false;
  if (nullt_FileB (&xfb->fb))
  {
    skipds_XFile (xf, 0);
    if (xf->buf.sz - xf->off < 50)
      xget_chunk_XFileB (xfb);
    s = xget_uint_cstr (x, cstr_XFile (xf));
    xfb->fb.good = !!s;
    if (!xfb->fb.good)  return false;
    xf->off = IdxElt( xf->buf.s, s );
  }
  else
  {
    union Castless {
      uint x;
      byte b[sizeof(uint)];
    } y;
    xfb->fb.good = xgetn_byte_XFileB (xfb, y.b, sizeof(uint));
    if (!xfb->fb.good)  return false;
    *x = y.x;
  }
  return true;
}

static
  bool
xgetn_raw_byte_XFileB (XFileB* xfb, byte* a, zuint n)
{
  XFile* const xf = &xfb->xf;
  Claim2( xfb->fb.fmt ,==, FileB_Raw );
  flush_XFileB (xfb);
  while (n > 0)
  {
    zuint m;
    if (xf->buf.sz == 0)
      xfb->fb.good = xget_chunk_XFileB (xfb);
    if (!xfb->fb.good)  return false;
    m = (n < xf->buf.sz ? n : xf->buf.sz);
    memcpy (a, xf->buf.s, m);
    xf->off = m;
    flush_XFileB (xfb);
    a = &a[m];
    n -= m;
  }
  return true;
}

  bool
xgetn_byte_XFileB (XFileB* xfb, byte* a, zuint n)
{
  if (xfb->fb.fmt == FileB_Raw)
    return xgetn_raw_byte_XFileB (xfb, a, n);

  while (n > 0)
  {
    uint y;
    xfb->fb.good = xget_uint_XFileB (xfb, &y);
    if (!xfb->fb.good)  return false;
    a[0] = (byte) y;
    a = &a[1];
    n -= 1;
  }
  return true;
}

  AlphaTab
textfile_AlphaTab (const char* pathname, const char* filename)
{
  const bool use_stdin = !pathname && !filename;
  XFileB* xfileb;
  XFileB xfileb_on_stack;
  AlphaTab text = dflt_AlphaTab ();
  if (use_stdin) {
    xfileb = stdin_XFileB ();
  }
  else {
    xfileb = &xfileb_on_stack;
    init_XFileB (xfileb);
    if (!open_FileB (&xfileb->fb, pathname, filename)) {
      lose_XFileB (xfileb);
      return text;
    }
  }

  if (!xget_XFileB (xfileb)) {
    lose_XFileB (xfileb);
    return text;
  }

  init_AlphaTab_move_XFile (&text, &xfileb->xf);

  if (use_stdin) {
    close_XFileB (xfileb);
  }
  else {
    lose_XFileB (xfileb);
  }
  return text;
}

