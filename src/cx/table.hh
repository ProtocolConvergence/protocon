/**
 * \file table.hh
 * Dynamic array.
 **/
#ifndef Table_HH_
#define Table_HH_
#include <cstddef>
#include <utility>
#include <vector>

namespace Cx {

/** Standard vector.*/
template <class T>
class Table : public std::vector<T>
{
public:
  Table() : std::vector<T>() {}
  Table(const Table<T>& a) : std::vector<T>(a) {}
  explicit Table(const std::vector<T>& a) : std::vector<T>(a) {}
  explicit Table(size_t n) : std::vector<T>(n) {}
  explicit Table(size_t n, const T& e) : std::vector<T>(n, e) {}
  Table<T>& operator=(const std::vector<T>& a) {
    this->assign(a.begin(), a.end());
    return *this;
  }
  virtual ~Table() {}

  size_t sz() const {return this->size();}
  bool empty_ck() const {return this->empty();}

  void grow(size_t capac, const T& e = T()) {
    this->insert(this->end(), capac, e);
  }

  void ensize(size_t capac) {
    if (capac > this->size()) {
      this->resize(capac);
    }
  }
  void wipe(const T& x) {
    this->assign(this->size(), x);
  }

  T* operator+() {return this->data();}
  const T* operator+() const {return this->data();}

  size_t index_of(const T* e) const {
    return e - this->data();
  }

  bool elem_ck(const T& e) const
  {
    for (size_t i = 0; i < this->size(); ++i) {
      if (e == (*this)[i]) {
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

  T& top() {return this->back();}
  const T& top() const {return this->back();}

  int cmp(const Table<T>& b) const
  {
    const Table<T>& a = *this;
    const size_t n = (a.size() <= b.size()) ? a.size() : b.size();
    for (size_t i = 0; i < n; ++i) {
      if (a[i] < b[i])  return -1;
      if (b[i] < a[i])  return  1;
    }
    if (a.size() < b.size())  return -1;
    if (b.size() < a.size())  return  1;
    return 0;
  }

  bool operator==(const Table<T>& b) const {
    return (0 == this->cmp(b));
  }
  bool operator!=(const Table<T>& b) const {
    return !(*this == b);
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

  void reverse() {
    size_t n = this->size() / 2;
    for (size_t i = 0; i < n; ++i) {
      std::swap((*this)[i], (*this)[this->size()-1-i]);
    }
  }
  bool remove(const T& e)
  {
    size_t pos = 0;
    for (size_t i = 0; i < this->size(); ++i) {
      if ((*this)[i] != e) {
        if (pos != i) {
          (*this)[pos] = (*this)[i];
        }
        pos += 1;
      }
    }
    if (pos != this->size()) {
      this->mpop(this->size() - pos);
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
  void add_domain(unsigned domsz) {
    Table<T>& state_map = *this;
    const size_t n = state_map.size();
    state_map.grow(n * (domsz-1));
    for (size_t i = n; i > 0; --i) {
      for (unsigned j = 0; j < domsz; ++j) {
        state_map[(i-1) * domsz + j] = state_map[i-1];
      }
    }
  }

};

inline
  void
state_of_index(unsigned* state, size_t idx, const Table<unsigned>& doms)
{
  for (unsigned i = doms.size(); i > 0; --i) {
    state[i-1] = idx % doms[i-1];
    idx /= doms[i-1];
  }
}

inline
  size_t
index_of_state(const unsigned* state, const Table<unsigned>& doms)
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
