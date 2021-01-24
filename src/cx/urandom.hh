
#ifndef URandom_HH_
#define URandom_HH_

#include "synhax.hh"
extern "C" {
#include "urandom.h"
}

namespace Cx {

namespace C {
  using ::URandom;
}

class URandom
{
private:
  C::URandom urandom;
  bool using_system_urandom;
public:
  URandom()
    : using_system_urandom(false)
  {
    init_URandom (&urandom);
  }
  URandom(uint pcidx, uint npcs)
    : using_system_urandom(false)
  {
    init2_URandom (&urandom, pcidx, npcs);
  }

  void use_system_urandom(bool b)
  {
    using_system_urandom = b;
  }

  uint pick(uint n)
  {
    if (using_system_urandom) {
      return randommod_sysCx (n);
    }
    return uint_URandom (&urandom, n);
  }

  template <typename T>
  void shuffle(T* a, uint n)
  {
    for (; n > 1; --n)
    {
      uint i = n-1;
      uint j = this->pick(n);
      SwapT( T, a[i], a[j] );
    }
  }
};
}

#endif

