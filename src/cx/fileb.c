/**
 * \file fileb.c
 * Simple and advanced file I/O and parsing.
 **/
#include "fileb.h"
#include "lace_compat_fd.h"

#include <assert.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>

static bool
xget_chunk_XFileB (XFileB* xfb);
static bool
xget_chunk_fn_XFileB (XFile* xf);
static bool
oput_chunk_OFileB (OFileB* ofb);
static void
oputn_raw_byte_OFileB (OFileB* ofb, const byte* a, zuint n);

static void
close_fn_XFileB (XFile* xf);
static void
close_fn_OFileB (OFile* of);
static void
free_fn_XFileB (XFile* xf);
static void
free_fn_OFileB (OFile* of);
static bool
flush_fn_OFileB (OFile* of);

const XFileVT FileB_XFileVT = DEFAULT3_XFileVT(xget_chunk_fn_XFileB, close_fn_XFileB, free_fn_XFileB);
const OFileVT FileB_OFileVT = DEFAULT3_OFileVT(flush_fn_OFileB, close_fn_OFileB, free_fn_OFileB);

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

  void
init_OFileB (OFileB* ofb)
{
  static OFileCtx ctx;
  init_OFile (&ofb->of);
  ofb->of.flushsz = BUFSIZ;
  ofb->of.mayflush = true;
  init_FileB (&ofb->fb, true);
  ofb->of.vt = &FileB_OFileVT;
  ofb->of.ctx = &ctx;
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
  Ensure0( f->xf.buf.s[0] );
  f->xf.buf.sz = 1;
}

  void
close_OFileB (OFileB* f)
{
  flush_OFileB (f);
  close_FileB (&f->fb);
  f->of.off = 0;
  Ensure0( f->of.buf.s[0] );
  f->of.buf.sz = 1;
}

  void
close_fn_XFileB (XFile* xf)
{
  close_XFileB (CastUp( XFileB, xf, xf ));
}

  void
close_fn_OFileB (OFile* of)
{
  close_OFileB (CastUp( OFileB, of, of ));
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
lose_OFileB (OFileB* ofb)
{
  close_OFileB (ofb);
  LoseTable( ofb->of.buf );
  lose_AlphaTab (&ofb->fb.pathname);
  lose_AlphaTab (&ofb->fb.filename);
}

  void
free_fn_XFileB (XFile* xf)
{
  XFileB* xfb = CastUp( XFileB, xf, xf );
  lose_XFileB (xfb);
  free (xfb);
}

  void
free_fn_OFileB (OFile* of)
{
  OFileB* ofb = CastUp( OFileB, of, of );
  lose_OFileB (ofb);
  free (ofb);
}

static inline
  zuint
chunksz_OFileB (OFileB* ofb)
{
  (void) ofb;
  return BUFSIZ;
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

  byte*
ensure_OFileB (OFileB* ofb, zuint n)
{
  OFile* const of = &ofb->of;
  oput_chunk_OFileB (ofb);
  EnsizeTable( of->buf, of->off+n );
  return &of->buf.s[of->off];
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

  void
setfmt_OFileB (OFileB* ofb, FileB_Format fmt)
{
  ofb->fb.fmt = fmt;
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

  lace_compat_fd_cloexec(fd);
  fb->fd = fd;
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
  lace_compat_fd_cloexec(fb->fd);
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


static
  bool
foput_OFileB (OFileB* ofb, const byte* a, uint n)
{
  size_t nout;
  nout = fwrite (a, 1, n, ofb->fb.f);
  return (nout == n);
}

static inline
  bool
selfcont_OFileB (OFileB* ofb)
{
  return (!ofb->fb.f);
}

static
  bool
flush1_OFileB (OFileB* ofb, const byte* a, uint n)
{
  OFile* const of = &ofb->of;
  bool good = true;
  if (selfcont_OFileB (ofb))
  {
    if (n == 0)  return true;
    GrowTable( of->buf, n );
    memcpy (&of->buf.s[of->off], a, n);
    of->off += n;
  }
  else
  {
    if (of->off > 0)
    {
      good = foput_OFileB (ofb, of->buf.s, of->off);
      if (!good)  return false;
      of->buf.sz = 1;
      of->off = 0;
    }
    if (n > 0)
    {
      good = foput_OFileB (ofb, a, n);
      if (!good)  return false;
    }
    fflush (ofb->fb.f);
  }


  if (nullt_FileB (&ofb->fb))
  {
    /* Not sure why...*/
    Ensure0( of->buf.s[of->off] );
  }
  return true;
}

  bool
flush_OFileB (OFileB* ofb)
{
  return flush1_OFileB (ofb, 0, 0);
}

  bool
flush_fn_OFileB (OFile* of)
{
  return flush_OFileB (CastUp( OFileB, of, of ));
}

  bool
oput_chunk_OFileB (OFileB* f)
{
  if (f->of.off < f->of.flushsz)  return true;
  /* In the future, we may not want to flush all the time!*/
  /* Also, we may not wish to flush the whole buffer.*/
  return flush_OFileB (f);
}

#if 0
  void
op_FileB (XOFileB* xo, FileB_Op op, FileBOpArg* arg)
{
  FileB* fb = CastUp( FileB, xo, xo );
  (void) arg;
  switch (op)
  {
    case FileB_XGetChunk:
      xget_chunk_FileB (fb);
      break;
    case FileB_OPutChunk:
      oput_chunk_FileB (fb);
      break;
    case FileB_FlushO:
      flusho_FileB (fb);
      break;
    case FileB_Close:
      close_FileB (fb);
      break;
    case FileB_NOps:
      Claim(0);
      break;
  }
}
#endif

  void
oputn_raw_byte_OFileB (OFileB* ofb, const byte* a, zuint n)
{
  OFile* const of = &ofb->of;
  const zuint ntotal = of->off + n;
  if (ntotal <= AllocszTable(of->buf))
  {
    memcpy (&of->buf.s[of->off], a, n);
    of->off = ntotal;

    if (of->off > of->buf.sz)
      of->buf.sz = of->off;
  }
  else if (ntotal <= 2*chunksz_OFileB (ofb))
  {
    EnsizeTable( of->buf, 2*chunksz_OFileB (ofb) );
    memcpy (&of->buf.s[of->off], a, n);
    of->off = ntotal;
  }
  else
  {
    flush1_OFileB (ofb, a, n);
  }
}

  void
oputn_byte_OFileB (OFileB* ofb, const byte* a, zuint n)
{
  uint i;
  if (ofb->fb.fmt == FileB_Raw)
  {
    oputn_raw_byte_OFileB (ofb, a, n);
    return;
  }
  for (i = 0; i < n; ++i) {
    oput_uint_OFile (&ofb->of, a[i]);
    if (i+1 < n)
      oput_char_OFile (&ofb->of, ' ');
  }
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

