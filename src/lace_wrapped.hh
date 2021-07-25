#ifndef LACE_WRAPPED_HH_
#define LACE_WRAPPED_HH_
extern "C" {
#include "lace.h"
}

#include <cstring>
#include <iostream>
#include <memory>
#include <mutex>

namespace lace {
class ofstream : private std::streambuf, public std::ostream
{
public:
  ofstream() : std::ostream(this) {}

  ofstream(const std::string& filename)
    : std::ostream(this)
    , out_(::open_LaceOF(filename.c_str()))
  {
    if (!out_) {setstate(std::ios::badbit);}
  }

  ofstream(::LaceO* out)
    : std::ostream(this)
    , out_(out)
  {
    if (!out_) {setstate(std::ios::badbit);}
  }

  void close() {
    out_.reset(NULL);
  }
  void open(const std::string& filename) {
    out_.reset(::open_LaceOF(filename.c_str()));
  }

private:
  int sync() override {
    std::unique_lock<std::mutex> exclusive_block(lock_);
    ::flush_LaceO(out_.get());
    return 0;
  }

  std::streamsize xsputn(const char* buf, std::streamsize size) override {
    std::unique_lock<std::mutex> exclusive_block(lock_);
    memcpy(grow_LaceO(out_.get(), size), buf, size);
    maybe_flush_LaceO(out_.get());
    return size;
  }

  int overflow(int c) override {
    std::unique_lock<std::mutex> exclusive_block(lock_);
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

  std::mutex lock_;
  std::unique_ptr<LaceO,DeleterForLaceO> out_;
};
}
#endif
