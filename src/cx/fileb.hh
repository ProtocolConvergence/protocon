
#ifndef FileB_HH_
#define FileB_HH_

#include "alphatab.hh"
#include "xfile.hh"
extern "C" {
#include "fileb.h"
}

namespace Cx {
namespace C {
  using ::XFileB;
}

class XFileB : public Cx::XFile
{
private:
  C::XFileB xfb;

public:
  XFileB()
    : XFile( &xfb.xf )
  {
    init_XFileB (&xfb);
  }
  ~XFileB()
  {
    lose_XFileB (&xfb);
  }

  bool open(const String& pathname, const String& filename) {
    return open_FileB (&xfb.fb, pathname.c_str(), filename.c_str());
  }
  bool open(const String& filename) {
    return this->open ("", filename);
  }

  /** Open a user-specified file, defaulting to stdout if the file is "-".
   *
   * \return The output file that must be used.
   *   It is wise to construct a Cx::XFile object with this.
   **/
  C::XFile* uopen(const String& dirname, const String& filename) {
    if (filename == "-") {
      return stdin_XFile ();
    }
    if (this->open(dirname, filename)) {
      return &xfb.xf;
    }
    return 0;
  }

  C::XFile* uopen(const String& filename) {
    return this->uopen("", filename);
  }

private:
  XFileB(const XFileB&);
  XFileB& operator=(const XFileB&);
};
}

#endif

