
#ifndef SYNHAX_HH_
#define SYNHAX_HH_

#include <map>
#include <string>
#include <vector>

using std::map;
using std::string;
using std::vector;

typedef unsigned int uint;

#ifdef _MSC_VER
# define __FUNC__ __FUNCTION__
#else
# define __FUNC__ __func__
#endif

#define ArraySz( a )  (sizeof(a) / sizeof(*a))

#define UFor( i, n )  for (uint i = 0; i < (n); ++i)

void
dbglog_printf3 (const char* file,
                const char* func,
                uint line,
                const char* fmt,
                ...);

#define DBog0(s)  dbglog_printf3 (__FILE__,__FUNC__,__LINE__,s)
#define DBog1(s,a)  dbglog_printf3 (__FILE__,__FUNC__,__LINE__,s,a)
#define DBog2(s,a,b)  dbglog_printf3 (__FILE__,__FUNC__,__LINE__,s,a,b)
#define DBog3(s,a,b,c)  dbglog_printf3 (__FILE__,__FUNC__,__LINE__,s,a,b,c)
#define DBog_ujint(x)  DBog2( "%s:%lu", #x, (ujint)(x) )

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


#endif

