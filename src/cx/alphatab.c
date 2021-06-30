
#include "lace.h"
#include "alphatab.h"
#include <stdio.h>

  char*
itoa_dup_cstr (int x)
{
  char buf[50];
  sprintf (buf, "%i", x);
  return dup_cstr (buf);
}

  char*
xget_uint_cstr (uint* ret, const char* in)
{
  zuint x = 0;
  char* s =
    xget_ujint_cstr (&x, in);
  if (!s)  return 0;
  if (x > UINT_MAX)  return 0;
  *ret = x;
  return s;
}

  char*
xget_int_cstr (int* ret, const char* in)
{
  return lace_parse_int(ret, in);
}

  char*
xget_luint_cstr (luint* ret, const char* in)
{
  unsigned long v;
  char* out = 0;

  assert (ret);
  assert (in);
  v = strtoul (in, &out, 10);

  if (out == in)  out = 0;
  if (out)
  {
    *ret = v;
    if (*ret != v)  out = 0;
  }
  return out;
}

char* xget_ujint_cstr (ujint* ret, const char* in) {
  luint x = 0;
  char* out = xget_luint_cstr (&x, in);
  assert(ret);
  *ret = x;
  return out;
}

  char*
xget_real_cstr (real* ret, const char* in)
{
  double v = 0;
  char* out = lace_parse_double(&v, in);
  if (out) {
    *ret = (real)v;
  }
  return out;
}

  Sign
cmp_AlphaTab (const AlphaTab* a, const AlphaTab* b)
{
  zuint na = a->sz;
  zuint nb = b->sz;
  int ret;
  if (na > 0 && !a->s[na-1])  --na;
  if (nb > 0 && !b->s[nb-1])  --nb;

  if (na <= nb)
  {
    ret = memcmp (a->s, b->s, na * sizeof(char));
    if (ret == 0 && na < nb)
      ret = -1;
  }
  else
  {
    ret = memcmp (a->s, b->s, nb * sizeof(char));
    if (ret == 0)
      ret = 1;
  }
  return sign_of (ret);
}

  Sign
cmp_cstr_loc (const char* const* a, const char* const* b)
{
  return cmp_cstr (*a, *b);
}

  void
cat_uint_AlphaTab (AlphaTab* a, uint x)
{
  char buf[50];
  (void) sprintf(buf, "%u", x);
  cat_cstr_AlphaTab (a, buf);
}

  void
cat_luint_AlphaTab (AlphaTab* a, luint x)
{
  char buf[50];
  (void) sprintf(buf, "%lu", x);
  cat_cstr_AlphaTab (a, buf);
}

  void
cat_int_AlphaTab (AlphaTab* a, int x)
{
  char buf[50];
  (void) sprintf(buf, "%d", x);
  cat_cstr_AlphaTab (a, buf);
}

