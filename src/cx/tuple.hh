#ifndef Tuple_HH_
#define Tuple_HH_

extern "C" {
#include "def.h"
}

namespace Cx {
template <class T, uint N>
class Tuple
{
public:
  T s[N];
  Tuple() {}
  Tuple(const T& a) {
    this->wipe(a);
  }
  T& operator[](uint i) {
    return s[i];
  }
  const T& operator[](uint i) const {
    return s[i];
  }

  bool operator==(const Tuple<T,N>& b) const {
    const Tuple<T,N>& a = *this;
    for (uint i = 0; i < N; ++i) {
      if (a[i] != b[i])  return false;
    }
    return true;
  }
  bool operator!=(const Tuple<T,N>& b) const {
    return !(*this == b);
  }

  Sign cmp(const Tuple<T,N>& b) const
  {
    const Tuple<T,N>& a = *this;
    for (uint i = 0; i < N; ++i) {
      if (a[i] < b[i])  return -1;
      if (b[i] < a[i])  return  1;
    }
    return 0;
  }

  bool operator<=(const Tuple<T,N>& b) const {
    return (this->cmp(b) <= 0);
  }
  bool operator<(const Tuple<T,N>& b) const {
    return (this->cmp(b) < 0);
  }
  bool operator>(const Tuple<T,N>& b) const {
    return (this->cmp(b) > 0);
  }
  bool operator>=(const Tuple<T,N>& b) const {
    return (this->cmp(b) >= 0);
  }

  void wipe(const T& x) {
    for (uint i = 0; i < N; ++i) {
      (*this)[i] = x;
    }
  }
};

template <class T>
class Triple : public Tuple<T,3>
{
public:
  Triple() : Tuple<T,3>() {}

  Triple(const T& e0, const T& e1, const T& e2)
    : Tuple<T,3>()
  {
    (*this)[0] = e0;
    (*this)[1] = e1;
    (*this)[2] = e2;
  }

  Triple(const T& e)
    : Tuple<T,3>()
  {
    (*this)[0] = e;
    (*this)[1] = e;
    (*this)[2] = e;
  }
};


template <class T>
  const Tuple<T,2>
mk_Tuple(const T& e0, const T& e1) {
  Tuple<T,2> tup;
  tup[0] = e0; tup[1] = e1;
  return tup;
}
template <class T>
  const Tuple<T,3>
mk_Tuple(const T& e0, const T& e1, const T& e2) {
  Tuple<T,3> tup;
  tup[0] = e0; tup[1] = e1; tup[2] = e2;
  return tup;
}
template <class T>
  const Tuple<T,4>
mk_Tuple(const T& e0, const T& e1, const T& e2, const T& e3) {
  Tuple<T,4> tup;
  tup[0] = e0; tup[1] = e1; tup[2] = e2; tup[3] = e3;
  return tup;
}

}
#endif
