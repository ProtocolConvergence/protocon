
#ifndef TEST_HH_
#define TEST_HH_

#include "cx/alphatab.hh"
#include "cx/set.hh"

namespace Cx {
  class OFile;
}

void Test(Cx::OFile& olog, const Cx::Set<Cx::String>& only);

#endif

