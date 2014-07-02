
#ifndef MpiDissem_HH_
#define MpiDissem_HH_

#include "mpidissemnet.hh"

class MpiDissem : public MpiDissemNet
{
public:

  MpiDissem(uint _PcIdx, uint NPcs, int _tag, MPI_Comm _comm);

public:
  bool xtestlite(Cx::Table<uint>& ret);
  bool xtest(Cx::Table<uint>& ret);
  bool xwait(Cx::Table<uint>& ret);

  MpiDissem& operator<<(uint x) {
    for (uint i = 0; i < this->o_sz(); ++i) {
      this->next_o_payloads[i].push(x);
    }
    return *this;
  }
};

#endif

