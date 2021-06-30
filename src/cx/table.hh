/**
 * \file table.hh
 * Dynamic array.
 **/
#ifndef Table_HH_
#define Table_HH_

#include "synhax.hh"
extern "C" {
#include "table.h"
}

namespace Cx {
namespace C {
  using ::Table;
}

/** Standard vector.*/
template <class T>
class Table
{
private:
  C::Table t;
public:
  Table() {
    t = dflt1_Table (sizeof(T));
  }
  Table(const Table<T>& a) {
    t = dflt1_Table (sizeof(T));
    for (zuint i = 0; i < a.sz(); ++i) {
      this->push(a[i]);
    }
  }
  explicit Table(const std::vector<T>& a) {
    t = dflt1_Table (sizeof(T));
    for (zuint i = 0; i < a.size(); ++i) {
      this->push(a[i]);
    }
  }
  const Table<T>& operator=(const Table<T>& a) {
    if (this->sz() > a.sz())
      this->mpop(this->sz() - a.sz());
    for (zuint  i = 0; i < this->sz(); ++i) {
      (*this)[i] = a[i];
    }
    while (this->sz() < a.sz()) {
      this->push(a[this->sz()]);
    }
    return *this;
  }
  const Table<T>& operator=(const std::vector<T>& a) {
    if (this->sz() > a.size())
      this->mpop(this->sz() - a.size());
    for (zuint  i = 0; i < this->sz(); ++i) {
      (*this)[i] = a[i];
    }
    while (this->sz() < a.size()) {
      this->push(a[this->sz()]);
    }
    return *this;
  }
  ~Table() {
    for (zuint i = 0; i < t.sz; ++i)
      (*this)[i].~T();
    lose_Table (&t);
  }

  explicit Table(zuint capac) {
    t = dflt1_Table (sizeof(T));
    this->grow(capac);
  }
  Table(zuint capac, const T& e) {
    t = dflt1_Table (sizeof(T));
    this->grow(capac, e);
  }

  zuint sz() const {
    return t.sz;
  }
  zuint size() const { return this->sz(); }

  bool empty_ck() const
  { return (t.sz == 0); }

  void affy(zuint capac) {
    zuint old_sz = this->sz();
    for (zuint i = capac; i < old_sz; ++i)
      (*this)[i].~T();
    affy_Table (&t, capac);
  }

  void affysz(zuint capac, const T& e = T()) {
    zuint old_sz = this->sz();
    for (zuint i = capac; i < old_sz; ++i)
      (*this)[i].~T();
    affysz_Table (&t, capac);
    for (zuint i = old_sz; i < t.sz; ++i) {
      new (&(*this)[i]) T(e);
    }
  }

  void grow(zuint capac, const T& e = T()) {
    zuint old_sz = t.sz;
    grow_Table (&t, capac);
    for (zuint i = old_sz; i < t.sz; ++i) {
      new (&(*this)[i]) T(e);
    }
  }

  void resize(zuint capac) {
    zuint old_sz = this->sz();
    for (zuint i = capac; i < old_sz; ++i)
      (*this)[i].~T();
    size_Table (&t, capac);
    for (zuint i = old_sz; i < capac; ++i)
      new (&(*this)[i]) T();
  }
  void ensize(zuint capac) {
    zuint old_sz = this->sz();
    for (zuint i = capac; i < old_sz; ++i)
      (*this)[i].~T();
    ensize_Table (&t, capac);
    for (zuint i = old_sz; i < capac; ++i)
      new (&(*this)[i]) T();
  }
  void wipe(const T& x) {
    for (zuint i = 0; i < this->sz(); ++i) {
      (*this)[i] = x;
    }
  }

  T& operator[](zuint i) {
    return *(T*) elt_Table (&t, i);
  }
  const T& operator[](zuint i) const {
    return *(const T*) elt_Table ((C::Table*)&t, i);
  }

  T* operator+() { return (T*) t.s; }
  const T* operator+() const { return (const T*) t.s; }

  zuint index_of(const T* e) const
  {
    return idxelt_Table(&t, e);
  }

  bool elem_ck(const T& e) const
  {
    for (zuint i = 0; i < t.sz; ++i) {
      if (e == (*this)[i])
        return true;
    }
    return false;
  }

  T& grow1() {
    T* e = (T*) grow1_Table (&t);
    new (e) T();
    return *e;
  }
  T& push(const T& x) {
    T* e = (T*) grow1_Table (&t);
    new (e) T(x);
    return *e;
  }
  Table<T>& operator<<(const T& x) {
    this->push(x);
    return *this;
  }
  void mpop(zuint n = 1) {
    for (zuint i = this->sz() - n; i < this->sz(); ++i)
      (*this)[i].~T();
    mpop_Table (&t, n);
  }
  void cpop(uint n = 1) {
    for (zuint i = this->sz() - n; i < this->sz(); ++i)
      (*this)[i].~T();
    cpop_Table (&t, n);
  }

  T& top() {
    return *(T*) top_Table (&t);
  }
  const T& top() const {
    return *(T*) top_Table ((C::Table*)&t);
  }

  bool operator==(const Table<T>& b) const {
    const Table<T>& a = *this;
    const zuint n = a.sz();
    if (n != b.sz())  return false;
    for (zuint i = 0; i < n; ++i) {
      if (a[i] != b[i])  return false;
    }
    return true;
  }
  bool operator!=(const Table<T>& b) const {
    return !(*this == b);
  }

  Sign cmp(const Table<T>& b) const
  {
    const Table<T>& a = *this;
    const zuint n = (a.sz() <= b.sz()) ? a.sz() : b.sz();
    for (zuint i = 0; i < n; ++i) {
      if (a[i] < b[i])  return -1;
      if (b[i] < a[i])  return  1;
    }
    if (a.sz() < b.sz())  return -1;
    if (b.sz() < a.sz())  return  1;
    return 0;
  }

  bool operator<=(const Table<T>& b) const {
    return (this->cmp(b) <= 0);
  }
  bool operator<(const Table<T>& b) const {
    return (this->cmp(b) < 0);
  }
  bool operator>(const Table<T>& b) const {
    return (this->cmp(b) > 0);
  }
  bool operator>=(const Table<T>& b) const {
    return (this->cmp(b) >= 0);
  }

  T* begin() {
    return (T*) elt_Table ((C::Table*)&t, 0);
  }
  T* end() {
    return (T*) elt_Table ((C::Table*)&t, t.sz);
  }
  const T* begin() const {
    return (T*) elt_Table ((C::Table*)&t, 0);
  }
  const T* end() const {
    return (T*) elt_Table ((C::Table*)&t, t.sz);
  }
  template <class Itr>
  void assign(Itr beg, Itr end)
  {
    this->clear();
    for (Itr it = beg; it != end; ++it) {
      this->push(*it);
    }
  }
  void reverse() {
    zuint n = this->sz() / 2;
    for (zuint i = 0; i < n; ++i)
      SwapT( T, (*this)[i], (*this)[this->sz()-1-i] );
  }
  bool remove(const T& e)
  {
    zuint pos = 0;
    for (zuint i = 0; i < this->sz(); ++i) {
      if ((*this)[i] != e) {
        if (pos != i) {
          (*this)[pos] = (*this)[i];
        }
        pos += 1;
      }
    }
    if (pos != this->sz()) {
      this->mpop(this->sz() - pos);
      return true;
    }
    return false;
  }
  void clear() {
    for (zuint i = 0; i < this->sz(); ++i)
      (*this)[i].~T();
    clear_Table (&this->t);
  }
  Table<T>& flush() {
    for (zuint i = 0; i < this->sz(); ++i)
      (*this)[i].~T();
    flush_Table (&this->t);
    return *this;
  }

  /** If this Table represents a mapping from state indices,
   * this method grows the state space to allow a new variable of
   * size /domsz/.
   *
   * \sa Cx::state_of_index()
   * \sa Cx::index_of_index()
   */
  void add_domain(uint domsz) {
    Table<T>& state_map = *this;
    const zuint n = state_map.sz();
    state_map.grow(n * (domsz-1));
    for (zuint i = n; i > 0; --i) {
      for (uint j = 0; j < domsz; ++j) {
        state_map[(i-1) * domsz + j] = state_map[i-1];
      }
    }
  }

};

template <class T>
  zuint
sz_of (const Table<T>& t)
{
  return t.sz();
}

inline
  void
state_of_index (uint* state, zuint idx, const Table<uint>& doms)
{
  ::state_of_index (state, idx, &doms[0], doms.sz());
}

inline
  zuint
index_of_state (const uint* state, const Table<uint>& doms)
{
  return ::index_of_state (state, &doms[0], doms.sz());
}
}

#endif
