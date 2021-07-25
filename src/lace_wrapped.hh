#ifndef LACE_WRAPPED_HH_
#define LACE_WRAPPED_HH_
extern "C" {
#include "lace.h"
}

#include <iostream>
#include <memory>

namespace lace {
class ofstream : private std::streambuf, public std::ostream
{
public:
  ofstream(const std::string& filename)
    : std::ostream(this)
    , out_(::open_LaceOF(filename.c_str()))
  {
    if (!out_) {
      setstate(std::ios::badbit);
    }
  }

  ofstream(::LaceO* out)
    : std::ostream(this)
    , out_(out)
  {
    if (!out_) {
      setstate(std::ios::badbit);
    }
  }

private:
  int overflow(int c) {
    ::putc_LaceO(out_.get(), (char)c);
    return 0;
  }

private:
  class DeleterForLaceO {
  public:
    void operator()(LaceO* out) {
      close_LaceO(out);
    }
  };

  std::unique_ptr<LaceO,DeleterForLaceO> out_;
};
}
#endif
