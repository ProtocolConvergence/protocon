
// THIS FILE IS NOT USED (yet)

#ifndef Associa_HH_
#define Associa_HH_

#include "synhax.hh"
extern "C" {
#include "associa.h"
}

namespace Cx {
namespace C {
  using ::Associa;
  using ::Assoc;;
}

template <class K>
  Sign
template_cmp_fn (const K* a, const K* b)
{
  if (*a < *b)  return -1;
  if (*a == *b)  return 0;
  return 1;
}

template <class K, class V>
class Map
{
private:
  C::Associa map;

public:

  Map()
  {
    InitAssocia( K, V, map, template_cmp_fn<K> );
  }

  ~Map()
  {
    for (C::Assoc* assoc = beg_Associa (&map);
         assoc;
         assoc = next_Assoc (assoc))
    {
      K* key = (K*) key_of_Assoc (&map, assoc);
      V* val = (V*) val_of_Assoc (&map, assoc);
      (*key).~K();
      (*val).~V();
    }
    lose_Associa (&map);
  }

  zuint sz() const { return map.nodes.sz; }

  V* lookup(const K& key)
  {
    C::Assoc* assoc = lookup_Associa (&map, &key);
    if (!assoc)  return 0;
    return (V*) val_of_Assoc (&map, assoc);
  }

  const V* lookup(const K& key) const
  {
    return ((Cx::Map*) this)->lookup(key);
  }

  Sign cmp(const K& a, const K& b) {
    return map.rbt.bst.cmp.fn (&a, &b);
  }
};

template <class K, class V>
  zuint
sz_of(const Map<K,V>& m)
{
  return m.sz();
}

}
using Cx::Map;

#endif

