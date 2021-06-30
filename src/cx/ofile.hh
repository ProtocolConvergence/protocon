
#ifndef OFile_HH_
#define OFile_HH_

#include "synhax.hh"
extern "C" {
#include "ofile.h"
}
#include "alphatab.hh"

namespace Cx {
namespace C {
  using ::OFile;
}

class OFile
{
private:
  C::OFile* ofile;

public:
  struct EndL {
    bool empty;
  };

  static EndL endl() { return EndL(); }

  OFile()
    : ofile( 0 )
  {}

  OFile(C::OFile* ofile)
  { this->ofile = ofile; }

  static OFile& null() {
    static OFile ofile( null_OFile () );
    return ofile;
  }

  bool operator!() const
  { return !ofile; }

  OFile& operator<<(int x)
  {
    oput_int_OFile (ofile, x);
    return *this;
  }
  OFile& operator<<(uint x)
  {
    oput_uint_OFile (ofile, x);
    return *this;
  }
  OFile& operator<<(luint x)
  {
    oput_luint_OFile (ofile, x);
    return *this;
  }
  OFile& operator<<(real x)
  {
    oput_real_OFile(ofile, x);
    return *this;
  }
  OFile& operator<<(char c)
  {
    oput_char_OFile (ofile, c);
    return *this;
  }
  OFile& operator<<(const char* s)
  {
    oput_cstr_OFile (ofile, s);
    return *this;
  }
  OFile& operator<<(const Cx::AlphaTab& s)
  {
    oput_AlphaTab (ofile, &s.t);
    return *this;
  }
  OFile& flush() {
    flush_OFile (ofile);
    return *this;
  }
  OFile& operator<<(const EndL& e)
  {
    (void) e;
    *this << '\n';
    this->flush();
    return *this;
  }

  void printf(const char* fmt, ...)
  {
    va_list args;
    va_start (args, fmt);
    vprintf_OFile (ofile, fmt, args);
    va_end (args);
  }

  void write(const char* s, zuint n)
  {
    oputn_char_OFile (ofile, s, n);
  }
};
}

#endif

