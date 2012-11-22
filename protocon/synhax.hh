
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

typedef unsigned int uint;
typedef unsigned long ujint;

#ifdef _MSC_VER
# define __FUNC__ __FUNCTION__
#else
# define __FUNC__ __func__
#endif


#define Stringify(a) #a

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
#define DBog4(s,a,b,c,d)  dbglog_printf3 (__FILE__,__FUNC__,__LINE__,s,a,b,c,d)
#define DBog5(s,a,b,c,d,e)  dbglog_printf3 (__FILE__,__FUNC__,__LINE__,s,a,b,c,d,e)
#define DBog_ujint(x)  DBog2( "%s:%lu", #x, (ujint)(x) )

#define Claim( x ) \
do { \
  if (!(x)) { \
    DBog1( "Failed Claim(): (%s)", #x ); \
  } \
} while (0)

#define Claim2( a, op, b )  Claim((a) op (b))

#define Claim2_uint( a, op, b ) \
do { \
  if (!((a) op (b))) { \
    DBog5( "FAILED: (%s) where (%s == %u) and (%s == %u)", Stringify((a) op (b)), #a, (uint) (a), #b, (uint) (b) ); \
  } \
} while (0)

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
  return a[a.size() - 1];
}

template <class T>
  T
Pop1(vector<T>& a)
{
  T x( a.back() );
  a.pop_back();
  return x;
}

#endif

