
#ifndef XFile_HH_
#define XFile_HH_

#include "synhax.hh"
extern "C" {
#include "xfile.h"
}

namespace Cx {
namespace C {
  using ::XFile;
}

class XFile
{
private:
  C::XFile* xfile;

public:
  bool allgood;

  XFile()
    : xfile( 0 )
    , allgood( true )
  {}
  XFile(C::XFile* xfile)
    : xfile( 0 )
    , allgood( true )
  {
    this->xfile = xfile;
  }

  bool good() const
  { return allgood; }

  bool operator!() const
  { return !xfile || !allgood; }

  XFile& operator>>(int& x)
  {
    bool good =
      xget_int_XFile (xfile, &x);
    allgood = allgood && good;
    return *this;
  }
  XFile& operator>>(uint& x)
  {
    bool good =
      xget_uint_XFile (xfile, &x);
    allgood = allgood && good;
    return *this;
  }
  XFile& operator>>(luint& x)
  {
    bool good =
      xget_luint_XFile (xfile, &x);
    allgood = allgood && good;
    return *this;
  }
  XFile& operator>>(char& c)
  {
    bool good =
      xget_char_XFile (xfile, &c);
    allgood = allgood && good;
    return *this;
  }

  bool skip(const char* pfx)
  {
    return skip_cstr_XFile(xfile, pfx);
  }
};
}

#endif
