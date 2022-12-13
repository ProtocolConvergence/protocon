#ifndef FILDESH_IFSTREAM_HH_
#define FILDESH_IFSTREAM_HH_
#include <fildesh/fildesh.h>

#include <cstring>
#include <istream>
#include <memory>
#include <mutex>

namespace fildesh {
class ifstream : private std::streambuf, public std::istream
{
public:
  ifstream() : std::istream(this) {
    setstate(std::ios::badbit);
  }

  ifstream(const std::string& filename)
    : std::istream(this)
    , in_(::open_FildeshXF(filename.c_str()))
  {
    if (!in_) {setstate(std::ios::badbit);}
  }

  ifstream(::FildeshX* in)
    : std::istream(this)
    , in_(in)
  {
    if (!in_) {setstate(std::ios::badbit);}
  }

  void close() {
    setstate(std::ios::badbit);
    in_.reset(NULL);
  }
  void open(const std::string& filename) {
    clear();
    in_.reset(::open_FildeshXF(filename.c_str()));
  }

private:
  std::streamsize xsgetn(char* buf, std::streamsize size) override;

  std::streambuf::int_type uflow() override {
    char buf[1];
    std::streamsize n = xsgetn(buf, 1);
    if (n == 0) {
      return std::streambuf::traits_type::eof();
    }
    return buf[0];
  }

  std::streambuf::int_type underflow() override {
    if (in_->off >= in_->size) {
      maybe_flush_FildeshX(in_.get());
      read_FildeshX(in_.get());
    }
    if (in_->off < in_->size) {
      return in_->at[in_->off];
    }
    return std::streambuf::traits_type::eof();
  }

private:
  class DeleterForFildeshX {
  public:
    void operator()(FildeshX* in) {
      close_FildeshX(in);
    }
  };

  std::mutex lock_;
  std::unique_ptr<FildeshX,DeleterForFildeshX> in_;
};
}
#endif
