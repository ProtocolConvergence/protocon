#ifndef AlphaTab_H_
static inline
  bool
eq_cstr(const char* a, const char* b)
{
  if (a == b) {
    return true;
  }
  if (!a || !b) {
    return false;
  }
  return (0 == strcmp(a, b));
}
#endif
