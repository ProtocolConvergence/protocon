
#include "xfile.h"
#include "alphatab.h"

  void
close_XFile (XFile* xf)
{
  VTCall( xf->vt, (void),close_fn,(xf) );
}

  void
lose_XFile (XFile* xf)
{
  LoseTable( xf->buf );
}

  void
free_XFile (XFile* xf)
{
  VTCall( xf->vt, (void),free_fn,(xf) );
}

  bool
xget_chunk_XFile (XFile* xf)
{
  uint sz = xf->buf.sz;
  VTCall( xf->vt, (void),xget_chunk_fn,(xf) );
  return (sz < xf->buf.sz);
}

  void
flush_XFile (XFile* f)
{
  TableT(byte)* buf = &f->buf;
  Claim2( f->off ,<=, buf->sz );

  if (!f->vt && f->off + 1 == buf->sz) {
    LoseTable( f->buf );
    InitZTable( f->buf );
    f->off = 0;
    f->flushsz = 1;
    return;
  }

  if (f->off == 0)  return;
  buf->sz = buf->sz - f->off;
  if (buf->sz > 0)
    memmove (buf->s, &buf->s[f->off], buf->sz);
  f->off = 0;
}

  void
xget_XFile (XFile* xf)
{
  bool more = true;
  while (more)
    more = xget_chunk_XFile (xf);
}

  char*
getline_XFile (XFile* in)
{
  uint ret_off;
  char* s;

  mayflush_XFile (in, May);
  ret_off = in->off;
  s = strchr (cstr_XFile (in), '\n');

  while (!s)
  {
    in->off = in->buf.sz - 1;
    if (!xget_chunk_XFile (in))  break;
    s = strchr (cstr_XFile (in), '\n');
  }

  if (s)
  {
    s[0] = '\0';
    in->off = IdxElt( in->buf.s, s );
    if (in->off > ret_off && s[-1] == '\r')
      s[-1] = '\0';
    if (in->off + 1 < in->buf.sz)
      in->off += 1;
  }
  else
  {
    in->off = in->buf.sz - 1;
  }

  return (ret_off + 1 == in->buf.sz) ? 0 : (char*) &in->buf.s[ret_off];
}

  bool
skiplined_XFile (XFile* xf, const char* delim)
{
  char* s;
  uint delim_sz = strlen (delim);

  mayflush_XFile (xf, May);
  s = strstr (cstr_of_XFile (xf), delim);

  while (!s)
  {
    /* We only need to re-check the last /delim_sz-1/ chars,
     * which start at /buf.sz-delim_sz/ due to the NUL byte.
     */
    if (xf->off + delim_sz < xf->buf.sz)
      xf->off = xf->buf.sz - delim_sz;

    mayflush_XFile (xf, May);
    if (!xget_chunk_XFile (xf))  break;

    s = strstr (cstr_of_XFile (xf), delim);
  }

  if (s) {
    s = &s[delim_sz];
    offto_XFile (xf, s);
  }
  else {
    xf->off = xf->buf.sz - 1;
  }

  mayflush_XFile (xf, May);
  return !!s;
}

/** Essentially strstr() on an XFile.**/
  char*
tolined_XFile (XFile* xf, const char* delim)
{
  const bool mayflush = xf->mayflush;
  const zuint off = xf->off;
  char* s = 0;

  xf->mayflush = false;
  if (skiplined_XFile (xf, delim))
    s = cstr1_of_XFile (xf, xf->off - strlen(delim));
  xf->off = off;
  xf->mayflush = mayflush;
  return s;
}

  char*
getlined_XFile (XFile* xf, const char* delim)
{
  char* s;
  uint ret_off;

  if (!delim)  return getline_XFile (xf);

  mayflush_XFile (xf, May);
  ret_off = xf->off;
  Claim2( ret_off ,<, xf->buf.sz );

  s = tolined_XFile (xf, delim);
  if (s)
  {
    const uint delim_sz = strlen (delim);
    memset(s, 0, delim_sz * sizeof(char));
    offto_XFile (xf, &s[delim_sz]);
    Claim2( xf->off ,<, xf->buf.sz );
  }
  else
  {
    xf->off = xf->buf.sz - 1;
  }

  return (ret_off + 1 == xf->buf.sz) ? 0 : (char*) &xf->buf.s[ret_off];
}


/** Assume opening delim has already been matched once.**/
  char*
tomatchd_XFile (XFile* xf, const char* beg_delim, const char* end_delim)
{
  uint nested = 1;
  const bool mayflush = xf->mayflush;
  const uint end_sz = strlen(end_delim);
  const zuint off = xf->off;
  char* pos = cstr_of_XFile (xf);

  while (nested > 0) {
    XFile olay[1];
    zuint window_end;
    pos = tolined_XFile (xf, end_delim);
    if (!pos)  break;
    -- nested;

    pos[0] = '\0';
    window_end = &pos[1] - cstr1_of_XFile (xf, 0);
    olay2_txt_XFile (olay, xf, xf->off, window_end);

    while (skiplined_XFile (olay, beg_delim)) {
      ++ nested;
    }
    pos[0] = end_delim[0];
    offto_XFile (xf, &pos[end_sz]);
  }
  xf->off = off;
  xf->mayflush = mayflush;
  return pos;
}

/** Assume opening delim has already been matched once.**/
  char*
getmatchd_XFile (XFile* xf, const char* beg_delim, const char* end_delim)
{
  char* end = tomatchd_XFile (xf, beg_delim, end_delim);
  if (end) {
    char* s = cstr_of_XFile (xf);
    const uint delim_sz = strlen (end_delim);
    memset(end, 0, delim_sz * sizeof(char));
    offto_XFile (xf, &end[delim_sz]);
    Claim2( xf->off ,<, xf->buf.sz );
    return s;
  }

  xf->off = xf->buf.sz - 1;
  return 0;
}

  void
skipds_XFile (XFile* xf, const char* delims)
{
  char* s;
  if (!delims)  delims = WhiteSpaceChars;
  mayflush_XFile (xf, May);
  s = (char*) &xf->buf.s[xf->off];
  s = &s[strspn (s, delims)];

  while (!s[0])
  {
    if (!xget_chunk_XFile (xf))  break;
    mayflush_XFile (xf, May);
    s = (char*) &xf->buf.s[xf->off];
    s = &s[strspn (s, delims)];
  }
  xf->off = IdxEltTable( xf->buf, s );
  mayflush_XFile (xf, May);
}

/**
 * Get text up to the next delimiter (or NUL) without modifying the stream
 * position or content.
 *
 * \param delims Delimiters to check against.
 *   For default whitespace delimiters, simply pass NULL.
 *   For only NUL delimiter, pass an empty string.
 *   To skip NUL delimiters, prepend the string with "!!".
 *   A string of "!!" exactly will use whitespace charaters without NUL.
 * \return A pointer to the next delimiter or the NUL at the end
 *   of this buffer if no such delimiter can be found in the stream.
 *   The returned pointer will never be NULL itself.
 **/
  char*
tods_XFile (XFile* xfile, const char* delims)
{
  zuint off;
  const bool skip_nul = pfxeq_cstr ("!!", delims);
  /* Fix up {delims} to not be NULL in any case,
   * and skip over the "!!" if it exists.
   */
  if (skip_nul && delims[2])
    delims = &delims[2];
  else if (!delims || skip_nul)
    delims = WhiteSpaceChars;

  mayflush_XFile (xfile, May);
  off = xfile->off;
  Claim2( off ,<, xfile->buf.sz );
  Claim( !xfile->buf.s[xfile->buf.sz-1] );

  while (off+1 < xfile->buf.sz ||
      xget_chunk_XFile (xfile))
  {
    /* Recompute {s} pointer after file read! */
    char* s = cstr1_of_XFile (xfile, off);
    off += (delims[0]  ?  strcspn (s, delims)  :  strlen (s));
    if (off+1 == xfile->buf.sz)  continue;

    s = cstr1_of_XFile (xfile, off);
    if (s[0] || !skip_nul)  return s;
    off += 1;
  }
  return cstr1_of_XFile (xfile, xfile->buf.sz-1);
}

/**
 * Read text up to the next delimiter and replace it with a NUL.
 *
 * The stream position is moved past the next delimiter.
 *
 * \param delims See tods_XFile() description.
 * \return The text starting at the current stream offset.
 *
 * \sa nextok_XFile()
 **/
  char*
nextds_XFile (XFile* xfile, char* ret_match, const char* delims)
{
  char* s = tods_XFile(xfile, delims);
  const zuint ret_off = xfile->off;

  offto_XFile (xfile, s);
  if (ret_match)  *ret_match = s[0];

  if (xfile->off+1 < xfile->buf.sz) {
    /* Nullify and step over the delimiter. */
    s[0] = '\0';
    xfile->off += 1;
  }
  else {
    Claim2( xfile->off ,<, xfile->buf.sz);
  }

  if (ret_off < xfile->off)
    return cstr1_of_XFile (xfile, ret_off);

  Claim2( ret_off ,==, xfile->off );
  return 0;
}


/**
 * Read the next token.
 *
 * \param xf Input stream whose position will shifted be past the next token.
 * \return The next token. Will be NULL if no such token exists.
 **/
  char*
nextok_XFile (XFile* xf, char* ret_match, const char* delims)
{
  skipds_XFile (xf, delims);
  return nextds_XFile (xf, ret_match, delims);
}

  void
replace_delim_XFile (XFile* xf, char delim)
{
  char* s = cstr_of_XFile (xf);
  if (!delim)  return;
  Claim2( xf->off ,>, 0 );
  s[-1] = delim;
}

/** Inject content from a file /src/
 * at the current read position of file /in/.
 * This allows a trivial implementation of #include.
 **/
  void
inject_XFile (XFile* in, XFile* src, const char* delim)
{
  uint delim_sz = strlen (delim);
  const zuint sz = in->buf.sz - in->off;

  xget_XFile (src);
  Claim2( src->buf.sz ,>, 0 );

  GrowTable( in->buf, src->buf.sz-1 + delim_sz );
  /* Make room for injection.*/
  memmove (&in->buf.s[in->off + src->buf.sz-1 + delim_sz],
      &in->buf.s[in->off],
      sz * sizeof (char));
  /* Inject file contents, assume src->buf.sz is strlen!*/
  memcpy (&in->buf.s[in->off],
      src->buf.s,
      (src->buf.sz-1) * sizeof (char));

  /* Add the delimiter at the end.*/
  if (delim_sz > 0)
    memcpy (&in->buf.s[in->off + src->buf.sz-1],
        delim,
        delim_sz * sizeof (char));
}

  bool
skip_cstr_XFile (XFile* xf, const char* pfx)
{
  uint n;
  if (!pfx)  return false;
  n = strlen (pfx);
  while (xf->off + n > xf->buf.sz)
  {
    if (!xget_chunk_XFile (xf))
      return false;
  }
  if (0 == strncmp (pfx, ccstr_of_XFile (xf), n))
  {
    xf->off += n;
    return true;
  }
  return false;
}

  void
olay_txt_XFile (XFile* olay, XFile* xf, zuint off)
{
  const zuint end = (xf->off + 1 < xf->buf.sz  ?  xf->off  :  xf->buf.sz);
  Claim2( off ,<, end );

  init_XFile (olay);
  olay->buf.s = &xf->buf.s[off];
  olay->buf.sz = end - off;

  Claim( !olay->buf.s[olay->buf.sz-1] );
  while (olay->buf.sz > 1 && !olay->buf.s[olay->buf.sz-2]) {
    olay->buf.sz -= 1;
  }
}

  bool
getlined_olay_XFile (XFile* olay, XFile* xf, const char* delim)
{
  char* s = getlined_XFile (xf, delim);
  if (!s)  return false;
  olay_txt_XFile (olay, xf, IdxEltTable( xf->buf, s ));
  return true;
}

  bool
getmatchd_olay_XFile (XFile* olay, XFile* xf, const char* beg_delim, const char* end_delim)
{
  char* s = getmatchd_XFile (xf, beg_delim, end_delim);
  if (!s)  return false;
  olay_txt_XFile (olay, xf, IdxEltTable( xf->buf, s ));
  return true;
}

  bool
nextds_olay_XFile (XFile* olay, XFile* xf, char* ret_match, const char* delims)
{
  char* s = nextds_XFile (xf, ret_match, delims);
  if (!s)  return false;
  olay_txt_XFile (olay, xf, IdxEltTable( xf->buf, s ));
  return true;
}

  bool
xget_int_XFile (XFile* xf, int* x)
{
  const char* s;
  skipds_XFile (xf, WhiteSpaceChars);
  tods_XFile (xf, WhiteSpaceChars);
  s = xget_int_cstr (x, (char*)&xf->buf.s[xf->off]);
  if (!s)  return false;
  xf->off = IdxElt( xf->buf.s, s );
  return true;
}

  bool
xget_uint_XFile (XFile* xf, uint* x)
{
  const char* s;
  skipds_XFile (xf, WhiteSpaceChars);
  tods_XFile (xf, WhiteSpaceChars);
  s = xget_uint_cstr (x, (char*)&xf->buf.s[xf->off]);
  if (!s)  return false;
  xf->off = IdxElt( xf->buf.s, s );
  return true;
}

  bool
xget_luint_XFile (XFile* xf, luint* x)
{
  const char* s;
  skipds_XFile (xf, WhiteSpaceChars);
  tods_XFile (xf, WhiteSpaceChars);
  s = xget_luint_cstr (x, (char*)&xf->buf.s[xf->off]);
  if (!s)  return false;
  xf->off = IdxElt( xf->buf.s, s );
  return true;
}

  bool
xget_ujint_XFile (XFile* xf, ujint* x) {
  const char* s;
  skipds_XFile (xf, WhiteSpaceChars);
  tods_XFile (xf, WhiteSpaceChars);
  s = xget_ujint_cstr (x, (char*)&xf->buf.s[xf->off]);
  if (!s)  return false;
  xf->off = IdxElt( xf->buf.s, s );
  return true;
}

  bool
xget_real_XFile (XFile* xf, real* x)
{
  const char* s;
  skipds_XFile (xf, WhiteSpaceChars);
  tods_XFile (xf, WhiteSpaceChars);
  s = xget_real_cstr (x, (char*)&xf->buf.s[xf->off]);
  if (!s)  return false;
  xf->off = IdxElt( xf->buf.s, s );
  return true;
}

  bool
xget_char_XFile (XFile* xf, char* c)
{
  if (xf->off + 1 == xf->buf.sz)
  {
    if (!xget_chunk_XFile (xf))
      return false;
  }
  *c = *cstr_XFile (xf);
  xf->off += sizeof(char);
  return true;
}

