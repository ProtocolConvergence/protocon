/**
 * \file alphatab.hh
 * Dynamic array.
 **/
#ifndef AlphaTab_HH_
#define AlphaTab_HH_
#include <string>

#include "synhax.hh"
extern "C" {
#include "alphatab.h"
}

namespace Cx {
class OFile;

namespace C {
  using ::AlphaTab;
}

class AlphaTab
{
private:
  C::AlphaTab t;
public:
  AlphaTab()
    : t( dflt_AlphaTab () )
  {}

  AlphaTab(const char* s)
    : t( cons1_AlphaTab (s) )
  {}

  explicit AlphaTab(const C::AlphaTab& b)
    : t( dflt_AlphaTab () )
  {
    copy_AlphaTab (&t, &b);
  }

  AlphaTab(const AlphaTab& b)
    : t( dflt_AlphaTab () )
  {
    copy_AlphaTab (&t, &b.t);
  }

  const AlphaTab& operator=(const C::AlphaTab& b) {
    copy_AlphaTab (&t, &b);
    return *this;
  }
  const AlphaTab& operator=(const AlphaTab& b) {
    return (*this = b.t);
  }
  ~AlphaTab() {
    lose_AlphaTab (&t);
  }

  void clear() { clear_AlphaTab (&t); }

  const char* data() const {
    return (char*)t.s;
  }

  size_t size() const {
    if (t.sz > 0) {
      if (t.s[t.sz-1] == '\0') {
        return t.sz-1;
      }
    }
    return t.sz;
  }

  AlphaTab& operator<<(char c) {
    cat_char_AlphaTab (&t, c);
    return *this;
  }

  AlphaTab& operator<<(const char* s) {
    cat_cstr_AlphaTab (&t, s);
    return *this;
  }

  AlphaTab& operator<<(const C::AlphaTab& b) {
    cat_AlphaTab (&t, &b);
    return *this;
  }

  AlphaTab& operator<<(const AlphaTab& b) {
    return (*this << b.t);
  }
  AlphaTab operator+(const AlphaTab& b) const {
    AlphaTab a( *this );
    a << b;
    return a;
  }

  AlphaTab& operator<<(uint x) {
    cat_uint_AlphaTab (&t, x);
    return *this;
  }
  const AlphaTab& operator=(uint x) {
    clear_AlphaTab (&t);
    return (*this) << x;
  }
  AlphaTab operator+(uint x) const {
    AlphaTab a( *this );
    a << x;
    return a;
  }

  AlphaTab& operator<<(zuint x) {
    cat_luint_AlphaTab (&t, x);
    return *this;
  }
  const AlphaTab& operator=(zuint x) {
    clear_AlphaTab (&t);
    return (*this) << x;
  }
  AlphaTab operator+(zuint x) const {
    AlphaTab a( *this );
    a << x;
    return a;
  }

  AlphaTab& operator<<(int x) {
    cat_int_AlphaTab (&t, x);
    return *this;
  }
  const AlphaTab& operator=(int x) {
    clear_AlphaTab (&t);
    return (*this) << x;
  }
  AlphaTab operator+(int x) const {
    AlphaTab a( *this );
    a << x;
    return a;
  }

  AlphaTab& push_delim(const char* pfx, const char* delim) {
    if (this->empty())
      (*this) = pfx;
    else
      (*this) << delim;
    return (*this);
  }
  AlphaTab& push_delim(const char* delim) {
    return push_delim(0, delim);
  }

  template <typename T>
  const AlphaTab& operator+=(const T& x) {
    return (*this << x);
  }

  bool operator==(const AlphaTab& b) const {
    return (0 == cmp_AlphaTab (&t, &b.t));
  }
  bool operator!=(const AlphaTab& b) const {
    return !(*this == b);
  }
  bool operator<(const AlphaTab& b) const {
    return (0 > cmp_AlphaTab (&t, &b.t));
  }

  operator std::string_view() const {
    if (this->empty()) {return "";}
    return std::string_view(this->data(), this->size());
  }
  const char* c_str() const {
    return ccstr_of_AlphaTab (&t);
  }
  bool empty() const {
    return (this->size() == 0);
  }

  friend class OFile;
  friend C::AlphaTab& operator<<(C::AlphaTab& a, const Cx::AlphaTab& b);
};

inline
C::AlphaTab& operator<<(C::AlphaTab& a, const Cx::AlphaTab& b)
{
  const C::AlphaTab tmp = dflt2_AlphaTab(b.c_str(), b.size());
  cat_AlphaTab (&a, &tmp);
  return a;
}

inline
std::ostream& operator<<(ostream& out, const AlphaTab& a) {
  if (a.size() > 0)
    out.write(a.data(), a.size());
  return out;
}

typedef AlphaTab String;
}

#endif

