/**
 * \file alphatab.hh
 **/
#ifndef AlphaTab_HH_
#define AlphaTab_HH_
#include <string>

extern "C" {
#include "table.h"
}

namespace Cx {

class AlphaTab
{
private:
  TableT(char) t = DEFAULT_Table;
public:
  AlphaTab() {}
  ~AlphaTab() {
    if (t.alloc_lgsz > 0 && t.alloc_lgsz != BITINT_MAX) {
      free(t.s);
    }
  }

  AlphaTab(const AlphaTab& b) {
    *this = b;
  }

  AlphaTab(const char* b) {
    *this = std::string_view(b);
  }
  AlphaTab(const std::string& b) {
    *this = std::string_view(b);
  }

  AlphaTab& operator=(std::string_view b) {
    if (t.sz <= b.size()) {
      grow_FildeshA_((void**)&t.s, &t.sz, &t.alloc_lgsz, 1, b.size() - t.sz);
    }
    else {
      mpop_FildeshA_((void**)&t.s, &t.sz, &t.alloc_lgsz, 1, t.sz - b.size());
    }
    if (t.sz > 0) {memcpy(t.s, b.data(), t.sz);}
    return *this;
  }
  const AlphaTab& operator=(const AlphaTab& b) {
    return (*this = std::string_view(b));
  }
  AlphaTab& operator=(const std::string& b) {
    return (*this = std::string_view(b));
  }
  AlphaTab& operator=(const char* b) {
    return (*this = std::string_view(b));
  }

  void clear() {
    mpop_FildeshA_((void**)&t.s, &t.sz, &t.alloc_lgsz, 1, t.sz);
  }

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

  AlphaTab& operator+=(std::string_view s) {
    t.sz = this->size();
    memcpy(
        grow_FildeshA_((void**)&t.s, &t.sz, &t.alloc_lgsz, 1, s.size()),
        s.data(), s.size());
    return *this;
  }
  AlphaTab& operator+=(char c) {
    return (*this += std::string_view(&c, 1));
  }
  AlphaTab operator+(std::string_view s) const {
    return (AlphaTab(*this) += s);
  }

  bool operator==(std::string_view b) const {
    return ((std::string_view)*this == b);
  }
  bool operator!=(std::string_view b) const {
    return ((std::string_view)*this != b);
  }
  bool operator<(std::string_view b) const {
    return ((std::string_view)*this < b);
  }

  operator std::string_view() const {
    if (this->empty()) {return "";}
    return std::string_view(this->data(), this->size());
  }
  const char* c_str() {
    *this += '\0';
    return t.s;
  }
  bool empty() const {
    return (this->size() == 0);
  }
};

inline
std::ostream& operator<<(ostream& out, const AlphaTab& a) {
  return (out << (std::string_view)a);
}

typedef AlphaTab String;
}

#endif

