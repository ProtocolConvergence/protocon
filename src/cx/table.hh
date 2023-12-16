/**
 * \file table.hh
 * Dynamic array.
 **/
#ifndef Table_HH_
#define Table_HH_
#include <vector>

#include "synhax.hh"

namespace Cx {

/** Standard vector.*/
template <class T>
class Table : public std::vector<T>
{
public:
  Table() = default;
  Table(Table<T>&& a) = default;
  Table(const Table<T>& a) = default;
  Table<T>& operator=(Table<T>&& a) = default;
  Table<T>& operator=(const Table<T>& a)  = default;
  virtual ~Table() = default;

  Table(std::vector<T>&& a) : std::vector<T>(std::move(a)) {}
  Table(const std::vector<T>& a) : std::vector<T>(a) {}
  explicit Table(size_t n) : std::vector<T>(n) {}
  explicit Table(size_t n, const T& e) : std::vector<T>(n, e) {}
  Table<T>& operator=(std::vector<T>&& a) {
    *dynamic_cast<std::vector<T>*>(this) = std::move(a);
    return *this;
  }
  Table<T>& operator=(const std::vector<T>& a) {
    *dynamic_cast<std::vector<T>*>(this) = a;
    return *this;
  }

  size_t sz() const {return this->size();}
  bool empty_ck() const {return this->empty();}

  void affy(size_t capac) {
    this->resize(capac);
  }
  void affysz(size_t capac, const T& e = T()) {
    if (this->size() < capac) {
      this->insert(this->end(), capac - this->size(), e);
    }
    else {
      this->resize(capac);
    }
  }

  void grow(size_t capac, const T& e = T()) {
    this->insert(this->end(), capac, e);
  }

  void ensize(size_t capac) {
    if (capac > this->size()) {
      this->resize(capac);
    }
  }
  void wipe(const T& x) {this->assign(this->size(), x);}

  T* operator+() {return this->data();}
  const T* operator+() const {return this->data();}

  size_t index_of(const T* e) const {return e - this->data();}

  bool elem_ck(const T& e) const
  {
    for (const auto& x : *this) {
      if (e == x) {
        return true;
      }
    }
    return false;
  }

  T& grow1() {
    return this->emplace_back();
  }
  T& push(const T& x) {
    this->push_back(x);
    return this->back();
  }
  Table<T>& operator<<(const T& x) {
    this->push_back(x);
    return *this;
  }
  void mpop(size_t n = 1) {
    this->resize(this->size() - n);
  }
  void cpop(size_t n = 1) {this->mpop(n);}
  void flush() {this->clear();}

  T& top() {return this->back();}
  const T& top() const {return this->back();}

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

inline
  void
state_of_index(unsigned* state, size_t idx, const std::vector<unsigned>& doms)
{
  for (unsigned i = doms.size(); i > 0; --i) {
    state[i-1] = idx % doms[i-1];
    idx /= doms[i-1];
  }
}

inline
  size_t
index_of_state(const unsigned* state, const std::vector<unsigned>& doms)
{
  size_t idx = 0;
  for (unsigned i = 0; i < doms.size(); ++i) {
    idx *= doms[i];
    idx += state[i];
  }
  return idx;
}

}

namespace protocon {
  using ::Cx::Table;
}

#endif
