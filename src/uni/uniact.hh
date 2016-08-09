#ifndef UniAct_HH_
#define UniAct_HH_

#include "cx/tuple.hh"

class UniAct : public Cx::Triple<uint>
{
public:
  UniAct() : Triple<uint>() {}
  UniAct(uint a, uint b, uint c) : Triple<uint>(a, b, c) {}
  UniAct(const uint* v) : Triple<uint>(v[0], v[1], v[2]) {}
  UniAct(uint a) : Triple<uint>(a) {}
};

#endif
