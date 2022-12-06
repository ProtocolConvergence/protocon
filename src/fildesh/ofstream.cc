
#include "ofstream.hh"
#include <cstring>

namespace fildesh {

std::streamsize ofstream::xsputn(const char* buf, std::streamsize size) {
  std::unique_lock<std::mutex> exclusive_block(lock_);
  memcpy(grow_FildeshO(out_.get(), size), buf, size);
  maybe_flush_FildeshO(out_.get());
  return size;
}

}  // namespace fildesh
