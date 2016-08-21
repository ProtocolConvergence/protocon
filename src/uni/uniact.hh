#ifndef UniAct_HH_
#define UniAct_HH_

#include "cx/tuple.hh"

typedef uint PcState;

class UniAct;
class UniStep;

class UniAct : public Cx::Triple<PcState>
{
public:
  UniAct() : Triple<PcState>() {}
  UniAct(PcState a, PcState b, PcState c) : Triple<PcState>(a, b, c) {}
  UniAct(const PcState* v) : Triple<PcState>(v[0], v[1], v[2]) {}
  explicit UniAct(PcState a) : Triple<PcState>(a) {}
};

class UniStep : public Cx::Tuple<PcState,2>
{
public:
  UniStep() : Tuple<PcState,2>() {}
  UniStep(PcState a, PcState c) : Tuple<PcState,2>() {
    (*this)[0] = a;
    (*this)[1] = c;
  }
};


#endif
