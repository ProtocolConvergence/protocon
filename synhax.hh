
#ifndef SYNHAX_HH_
#define SYNHAX_HH_

#include <iostream>
#include <map>
#include <string>
#include <utility>
#include <vector>

using std::map;
using std::pair;
using std::vector;
using std::string;
using std::ostream;

extern "C" {
#include "cx/def.h"
}

template <class K, class V>
  const V*
MapLookup(const map<K,V>& m, const K& key)
{
  typename map<K,V>::const_iterator it = m.find(key);
  if (it == m.end())  return NULL;
  return &it->second;
}

template <class K, class V>
  V*
MapLookup(map<K,V>& m, const K& key)
{
  typename map<K,V>::iterator it = m.find(key);
  if (it == m.end())  return NULL;
  return &it->second;
}

template <class T>
  T&
Grow1(vector<T>& a)
{
  a.resize(a.size() + 1);
  return a.back();
}

template <class T>
  T
Pop1(vector<T>& a)
{
  T x( a.back() );
  a.pop_back();
  return x;
}

template <class T>
  bool
Remove1(vector<T>& a, const T& elem)
{
  typename vector<T>::iterator it;
  for (it = a.begin(); it != a.end(); ++it) {
    if (*it == elem) {
      a.erase(it);
      return true;
    }
  }
  return false;
}

#endif

