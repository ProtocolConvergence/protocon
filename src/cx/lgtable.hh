/**
 * \file lgtable.hh
 * Dynamic array which does not relocate objects in memory.
 **/
#ifndef LgTable_HH_
#define LgTable_HH_

#include "synhax.hh"
extern "C" {
#include "lgtable.h"
}

namespace Cx {
namespace C {
  using ::LgTable;
}

/** Table that does not reallocate existing elements.
 *
 * Due to its nature, the LgTable does not store elements contiguously.
 */
template <class T>
class LgTable
{
private:
  C::LgTable t;
public:
  LgTable() {
    t = dflt1_LgTable (sizeof(T));
  }

  zuint begidx() const {
    return begidx_LgTable (&t);
  }
  zuint nextidx(zuint idx) const {
    return nextidx_LgTable (&t, idx);
  }
  bool endidx_ck(zuint idx) const {
    return endidx_ck_LgTable (&t, idx);
  }

  ~LgTable() {
    for (zuint i = begidx(); i != SIZE_MAX; i = nextidx(i))
      (*this)[i].~T();
    lose_LgTable (&t);
  }

  zuint sz() const {
    return t.sz;
  }

  const T& operator[](zuint i) const {
    return *(const T*) elt_LgTable ((C::LgTable*)&t, i);
  }
  T& operator[](zuint i) {
    return *(T*) elt_LgTable (&t, i);
  }

  zuint takeidx() {
    zuint idx = takeidx_LgTable (&t);
    new (&(*this)[idx]) T();
    return idx;
  }
  void giveidx(zuint idx) {
    (*this)[idx].~T();
    giveidx_LgTable (&t, idx);
  }

  void clear()
  {
    for (zuint i = begidx(); i != SIZE_MAX; i = nextidx(i))
    {
      (*this)[i].~T();
      giveidx_LgTable (&t, i);
    }
  }

  T& grow1() {
    T* e = (T*) take_LgTable (&t);
    new (e) T();
    return *e;
  }
  T& push(const T& x) {
    T* e = (T*) take_LgTable (&t);
    new (e) T(x);
    return *e;
  }

  T& top() {
    return (*this)[t.sz-1];
  }
  const T& top() const {
    return (*this)[t.sz-1];
  }

  LgTable<T>& operator=(const LgTable<T>& b) {
    LgTable<T>& a = *this;
    if (&a == &b)  return a;
    a.clear();
    for (zuint i = b.begidx(); i != SIZE_MAX; i = b.nextidx(i))
      a[a.takeidx()] = b[i];;
    return a;
  }

  zuint index_of(const T* e) const
  {
    return idxelt_LgTable(&t, e);
  }
};

template <class T>
  zuint
sz_of (const LgTable<T>& t)
{
  return t.sz();
}
}

#endif

