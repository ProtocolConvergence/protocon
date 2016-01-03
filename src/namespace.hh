
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
  class OFile;
  template <class T> class Set;
  template <class T> class Table;
  template <class T, uint N> class Tuple;
  class URandom;
  class XFile;

  template <class T> const Tuple<T,2> mk_Tuple(const T& e0, const T& e1);
}

namespace X {
  class Fmlae;
  class FmlaeCtx;
}

namespace PROJECT_NAMESPACE {
  typedef Cx::AlphaTab String;
  using Cx::BitTable;
  using Cx::FlatSet;
  using Cx::LgTable;
  using Cx::Map;
  using Cx::Mem;
  using Cx::OFile;
  using Cx::Set;
  using Cx::Table;
  using Cx::Tuple;
  using Cx::URandom;
  using Cx::XFile;

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
    class Net;
    class Sys;
  }

  using Cx::mk_Tuple;

