/**
 * \file alphatab.hh
 * Dynamic array.
 **/
#ifndef AlphaTab_HH_
#define AlphaTab_HH_

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

  void moveq(const C::AlphaTab& b) {
    lose_AlphaTab (&t);
    t = b;
  }

  char* forget() { return forget_AlphaTab (&t); }
  void clear() { clear_AlphaTab (&t); }
  void flush() { flush_AlphaTab (&t); }

  zuint sz() const {
    return t.sz;
  }
  bool operator!() const {
    return null_ck_AlphaTab (&t);
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
    if (this->empty_ck())
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

  const char* ccstr() const {
    return ccstr_of_AlphaTab (&t);
  }
  const char* cstr() const {
    return ccstr_of_AlphaTab (&t);
  }
  char* cstr() {
    return cstr_AlphaTab (&t);
  }
  bool null_ck() const {
    return null_ck_AlphaTab (&t);
  }
  bool empty_ck() const {
    return empty_ck_AlphaTab (&t);
  }

  friend class OFile;
  friend C::AlphaTab& operator<<(C::AlphaTab& a, const Cx::AlphaTab& b);
};

inline
C::AlphaTab& operator<<(C::AlphaTab& a, const Cx::AlphaTab& b)
{
  const C::AlphaTab tmp = dflt2_AlphaTab (b.cstr(), b.sz());
  cat_AlphaTab (&a, &tmp);
  return a;
}

inline
std::ostream& operator<<(ostream& out, const AlphaTab& a) {
  if (a.sz() > 0)
    out.write(a.cstr(), a.sz()-1);
  return out;
}

typedef AlphaTab String;
}

#endif

