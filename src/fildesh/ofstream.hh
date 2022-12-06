#ifndef FILDESH_OFSTREAM_HH_
#define FILDESH_OFSTREAM_HH_
#include <fildesh/fildesh.h>

#include <ostream>
#include <memory>
#include <mutex>

namespace fildesh {
class ofstream : private std::streambuf, public std::ostream
{
public:
  ofstream() : std::ostream(this) {
    setstate(std::ios::badbit);
  }

  ofstream(const std::string& filename)
    : std::ostream(this)
    , out_(::open_FildeshOF(filename.c_str()))
  {
    if (!out_) {setstate(std::ios::badbit);}
  }

  ofstream(::FildeshO* out)
    : std::ostream(this)
    , out_(out)
  {
    if (!out_) {setstate(std::ios::badbit);}
  }

  void close() {
    setstate(std::ios::badbit);
    out_.reset(NULL);
  }
  void open(const std::string& filename) {
    clear();
    out_.reset(::open_FildeshOF(filename.c_str()));
  }

private:
  int sync() override {
    std::unique_lock<std::mutex> exclusive_block(lock_);
    ::flush_FildeshO(out_.get());
    return 0;
  }

  std::streamsize xsputn(const char* buf, std::streamsize size) override;

  int overflow(int c) override {
    std::unique_lock<std::mutex> exclusive_block(lock_);
    ::putc_FildeshO(out_.get(), (char)c);
    return 0;
  }

private:
  class DeleterForFildeshO {
  public:
    void operator()(FildeshO* out) {
      close_FildeshO(out);
    }
  };

  std::mutex lock_;
  std::unique_ptr<FildeshO,DeleterForFildeshO> out_;
};
}
#endif
