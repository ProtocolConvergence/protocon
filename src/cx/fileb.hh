
#ifndef FileB_HH_
#define FileB_HH_

#include "ofile.hh"
#include "xfile.hh"
extern "C" {
#include "fileb.h"
}

namespace Cx {
namespace C {
  using ::OFileB;
  using ::XFileB;
}
class OFileB : public Cx::OFile
{
private:
  C::OFileB ofb;

public:
  OFileB()
    : OFile( &ofb.of )
  {
    init_OFileB (&ofb);
  }
  ~OFileB()
  {
    lose_OFileB (&ofb);
  }

  bool open(const String& pathname, const String& filename) {
    return open_FileB (&ofb.fb, pathname.cstr(), filename.cstr());
  }
  bool open(const String& filename) {
    return this->open ("", filename);
  }

  /** Open a user-specified file, defaulting to stdout if the file is "-".
   *
   * \return The output file that must be used.
   *   It is wise to construct a Cx::OFile object with this.
   **/
  C::OFile* uopen(const String& dirname, const String& filename) {
    if (filename == "-") {
      return stdout_OFile ();
    }
    if (filename == "/dev/stdout") {
      return stdout_OFile ();
    }
    if (filename == "/dev/stderr") {
      return stderr_OFile ();
    }
    if (this->open(dirname, filename)) {
      return &ofb.of;
    }
    return 0;
  }

  C::OFile* uopen(const String& filename) {
    return this->uopen("", filename);
  }

private:
  OFileB(const OFileB&);
  OFileB& operator=(const OFileB&);
};

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
    return open_FileB (&xfb.fb, pathname.cstr(), filename.cstr());
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

