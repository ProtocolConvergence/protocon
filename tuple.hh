
#ifndef Tuple_HH_
#define Tuple_HH_

namespace Cx {
template <class T, uint N>
class Tuple
{
public:
  T s[N];
  Tuple() {}
  Tuple(const T& a) {
    this->fill(a);
  }
  Tuple(const T& a, const T& b) {
    s[0] = a;
    s[1] = b;
  }
  T& operator[](uint i) {
    return s[i];
  }
  const T& operator[](uint i) const {
    return s[i];
  }
  bool operator==(const Tuple& b) const {
    const Tuple& a = *this;
    for (uint i = 0; i < N; ++i) {
      if (a[i] != b[i])  return false;
    }
    return true;
  }
  bool operator!=(const Tuple& b) const {
    const Tuple& a = *this;
    return !(a == b);
  }
  bool operator<(const Tuple& b) const {
    const Tuple& a = *this;
    for (uint i = 0; i < N; ++i) {
      if (a[i] < b[i])  return true;
      if (a[i] > b[i])  return false;
    }
    return false;
  }
  bool operator>(const Tuple& b) const {
    const Tuple& a = *this;
    return b < (*this);
  }
  bool operator<=(const Tuple& b) const {
    const Tuple& a = *this;
    return !(b < a);
  }
  bool operator>=(const Tuple& b) const {
    const Tuple& a = *this;
    return b <= a;
  }

  void fill(const T& x) {
    for (uint i = 0; i < N; ++i) {
      s[i] = x;
    }
  }
};
}
#endif

