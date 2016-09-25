#ifndef UniAct_HH_
#define UniAct_HH_

#include "cx/tuple.hh"
#include <stdlib.h>

typedef byte PcState;

class UniAct;
class UniStep;

class UniAct : public Cx::Triple<PcState>
{
public:
  UniAct() : Cx::Triple<PcState>() {}
  UniAct(PcState a, PcState b, PcState c) : Cx::Triple<PcState>(a, b, c) {}
  UniAct(const PcState* v) : Cx::Triple<PcState>(v[0], v[1], v[2]) {}
  explicit UniAct(PcState a) : Cx::Triple<PcState>(a) {}

  static UniAct of_id(uint actid, const uint domsz);
};

class UniStep : public Cx::Tuple<PcState,2>
{
public:
  UniStep() : Cx::Tuple<PcState,2>() {}
  UniStep(PcState a, PcState c) : Cx::Tuple<PcState,2>() {
    (*this)[0] = a;
    (*this)[1] = c;
  }

  static UniStep of_id(uint stepid, const uint domsz);
};


inline
  UniAct
UniAct::of_id(uint actid, const uint domsz)
{
  const div_t lo = div(actid, domsz);
  const div_t hi = div(lo.quot, domsz);
  return UniAct(hi.quot, hi.rem, lo.rem);
}

inline
  UniStep
UniStep::of_id(uint stepid, const uint domsz)
{
  const div_t d = div(stepid, domsz);
  return UniStep(d.quot, d.rem);
}

inline
  uint
id_of2(uint a, uint b, uint domsz)
{
  Claim( a < domsz );
  Claim( b < domsz );
  return a * domsz + b;
}

inline
  uint
id_of3(uint a, uint b, uint c, uint domsz)
{
  Claim( a < domsz );
  Claim( b < domsz );
  Claim( c < domsz );
  return (a * domsz + b) * domsz + c;
}

inline uint id_of(const Cx::Tuple<uint,2>& u, const uint domsz)
{ return id_of2(u[0], u[1], domsz); }

inline uint id_of(const Cx::Tuple<byte,2>& u, const uint domsz)
{ return id_of2(u[0], u[1], domsz); }

inline uint id_of(const Cx::Tuple<uint,3>& u, const uint domsz)
{ return id_of3(u[0], u[1], u[2], domsz); }

inline uint id_of(const Cx::Tuple<byte,3>& u, const uint domsz)
{ return id_of3(u[0], u[1], u[2], domsz); }

#endif
