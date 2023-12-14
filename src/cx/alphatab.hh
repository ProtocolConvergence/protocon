/**
 * \file alphatab.hh
 **/
#ifndef AlphaTab_HH_
#define AlphaTab_HH_
#include <string>

namespace Cx {

class AlphaTab : public std::string
{
public:
  AlphaTab& operator=(std::string_view b) {
    this->assign(b);
    return *this;
  }
  AlphaTab& operator=(const AlphaTab& b) {return *this = (std::string_view)b;}
  AlphaTab& operator=(const std::string& b) {return *this = (std::string_view)b;}
  AlphaTab& operator=(const char* b) {return *this = std::string_view(b);}

  AlphaTab() {}
  AlphaTab(const AlphaTab& b) : std::string(b.data(), b.size()) {}
  AlphaTab(const std::string& b) : std::string(b) {}
  AlphaTab(const char* b) : std::string(b) {}
  virtual ~AlphaTab() {}
};

}
namespace protocon {
typedef ::Cx::AlphaTab String;
}

#endif

