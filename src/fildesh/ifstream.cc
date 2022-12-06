
#include "ifstream.hh"
#include <cstring>

namespace fildesh {

std::streamsize ifstream::xsgetn(char* buf, std::streamsize size) {
  std::unique_lock<std::mutex> exclusive_block(lock_);
  if (in_->off >= in_->size) {
    maybe_flush_FildeshX(in_.get());
    read_FildeshX(in_.get());
  }
  if ((std::streamsize)(in_->size - in_->off) < size) {
    size = in_->size - in_->off;
  }
  memcpy(buf, &in_->at[in_->off], size);
  in_->off += size;
  maybe_flush_FildeshX(in_.get());
  return size;
}

}  // namespace fildesh
