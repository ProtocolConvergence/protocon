/**
 * \file alphatab.hh
 **/
#ifndef AlphaTab_HH_
#define AlphaTab_HH_
#include <cstring>
#include <string>

#include <fildesh/fildesh.h>

namespace Cx {

class AlphaTab
{
private:
  DECLARE_DEFAULT_FildeshAT(char, t_);

public:
  const char* data() const {return *t_;}
  size_t size() const {return count_of_FildeshAT(t_);}
  bool empty() const {return (this->size() == 0);}
  operator std::string_view() const {
    if (this->empty()) {return std::string_view("", 0);}
    return std::string_view(this->data(), this->size());
  }

  AlphaTab& operator=(std::string_view b) {
    resize_FildeshAT(t_, b.size());
    if (!b.empty()) {
      memcpy(*t_, b.data(), b.size());
    }
    return *this;
  }
  AlphaTab& operator=(const AlphaTab& b) {
    return (*this = (std::string_view)b);
  }
  AlphaTab& operator=(const std::string& b) {
    return (*this = (std::string_view)b);
  }
  AlphaTab& operator=(const char* b) {
    return (*this = std::string_view(b));
  }

  AlphaTab() {}
  AlphaTab(const AlphaTab& b) {*this = (std::string_view)b;}
  AlphaTab(const std::string& b) {*this = (std::string_view)b;}
  AlphaTab(const char* b) {*this = std::string_view(b);}
  ~AlphaTab() {close_FildeshAT(t_);}

  void clear() {
    clear_FildeshAT(t_);
  }

  AlphaTab& operator+=(std::string_view s) {
    if (!s.empty()) {
      memcpy(grow_FildeshAT(t_, s.size()), s.data(), s.size());
    }
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

  const char* c_str() {
    *this += '\0';
    mpop_FildeshAT(t_, 1);
    return *t_;
  }
};

inline
std::ostream& operator<<(ostream& out, const AlphaTab& a) {
  return (out << (std::string_view)a);
}

}
namespace protocon {
#if 1
typedef ::Cx::AlphaTab String;
#else
typedef std::string String;
#endif
}

#endif

