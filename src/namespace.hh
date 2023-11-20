
#ifndef END_NAMESPACE
#define END_NAMESPACE }
#endif

namespace Cx {
  class PFmla;
  class IntPFmla;
  class PFmlaVbl;
  class PFmlaCtx;

  class AlphaTab;
  class BitTable;
  template <class T> class FlatSet;
  template <class T> class LgTable;
  template <class K, class V> class Map;
  template <class T> class Mem;
  template <class T> class Set;
  template <class T> class Table;
  template <class T, unsigned N> class Tuple;
  template <class T> class Triple;
  class URandom;

  template <class T> const Tuple<T,2> mk_Tuple(const T& e0, const T& e1);
}

namespace X {
  class Fmlae;
  class FmlaeCtx;
}

#ifndef PROTOCON_NAMESPACE
#define PROTOCON_NAMESPACE protocon
#endif
namespace PROTOCON_NAMESPACE {
  typedef unsigned Action_id;

  typedef Cx::AlphaTab String;
  using Cx::BitTable;
  using Cx::FlatSet;
  using Cx::LgTable;
  using Cx::Map;
  using Cx::Mem;
  using Cx::Set;
  using Cx::Table;
  using Cx::Tuple;
  using Cx::Triple;

  using Cx::URandom;

  using Cx::IntPFmla;
  using Cx::PFmlaVbl;
  using Cx::PFmlaCtx;
  namespace P {
    typedef Cx::PFmla Fmla;
  }
  namespace X {
    typedef Cx::PFmla Fmla;
    using ::X::Fmlae;
    using ::X::FmlaeCtx;
  }

  namespace Xn {
    class VblSymmSpec;
    class PcSymmSpec;
    class Spec;
    class Vbl;
    class VblSymm;
    class ActSymm;
    class Pc;
    class PcSymm;
    class Net;
    class Sys;
  }

  using Cx::mk_Tuple;

