/**
 * \file synhax.h
 * All important macros.
 *
 * Included from def.h.
 **/
#ifndef __OPENCL_VERSION__
#include <assert.h>
#endif

#define Stringify(a) #a
#define Concatify(a,b) a ## b
#define ConcatifyDef(a,b)  Concatify(a,b)

/** Get size of an array (allocated on the stack in your current scope).**/
#define ArraySz( a )  (sizeof(a) / sizeof(*a))

/** Given some memory address and some offset,
 * cast the resulting memory address to a pointer of some type.
 */
#define CastOff( T, p ,op, off ) \
  ((T*) ((uintptr_t) (p) op (ptrdiff_t) (off)))

/** Call a virtual function.**/
#define VTCall(vt,pfx,fn,sfx) \
  do { \
    if ((vt) && (vt)->fn) { \
      pfx (vt)->fn sfx; \
    } \
  } while (0)

/** Given the memory address of a structure's field,
 * get the address of the structure.
 * \param T      Type.
 * \param field  Name of the field.
 * \param p      Memory address of the field.
 **/
#define CastUp( T, field, p ) \
  CastOff( T, p ,-, offsetof( T, field ) )

#define EltZ( a, idx, elsz ) \
  ((void*) ((uintptr_t) a + (uintptr_t) ((idx) * (elsz))))

#define Elt( a, idx )  (&(a)[idx])

#define EltInZ( a, e, n, elsz ) \
  (((uintptr_t) (a) <= (uintptr_t) (e)) && \
   ((uintptr_t) (e) < ((uintptr_t) (a) + (n * elsz))))

#define IdxEltZ( a, e, elsz ) \
  ((size_t) ((uintptr_t) (e) - (uintptr_t) (a)) / (elsz))

#define IdxElt( a, e ) \
  IdxEltZ( a, e, sizeof(*a) )

/** Ceiling of integer division.
 * \param a  Dividend.
 * \param b  Divisor.
 **/
#define ceil_quot( a, b ) \
  (((a) + ((b) - 1)) / (b))

#define CeilQuot( a, b )  ceil_quot(a,b)

#define InitDomMax( a )  do { a = 0; a = ~(a); } while (0)

#define BSfx( a, op, b, sfx )  (a)sfx op (b)sfx

#define UFor( i, bel )  for (i = 0; i < (bel); ++i)

#define AccepTok( line, tok ) \
  ((0 == strncmp ((line), (tok), strlen(tok))) \
   ? ((line) = &(line)[strlen(tok)]) \
   : 0)

/** Declare a variable pointing to an "anonymous" object on the stack
 * and initialize that object.
 * \param T  Type of variable when dereferenced.
 * \param x  Name of variable.
 * \param v  Initial value for the object.
 **/
#define DecloStack1( T, x, v ) \
  T onstack_##x = (v); T* const restrict x = &onstack_##x

/** Allocate memory via malloc() with less casting.
 * \param T  Type.
 * \param n  Number of elements.
 * \return  NULL when the number of elements is zero.
 **/
#define AllocT( T, n ) \
  ((n) == 0 ? (T*) 0 : \
   (T*) malloc ((n) * sizeof (T)))

#define CopyTo( a, b )  memcpy (&(a), &(b), sizeof(b))

/** Copy {b} to {a}.**/
#define Replac( a, b, n )  do \
{ \
  if ((n) > 0 && a && b) { \
    memcpy (a, b, (n) * sizeof (*b)); \
  } \
} while (0)

#define AllocTo( a, n ) do \
{ \
  const size_t AllocTo_sz = (n)*sizeof(*a); \
  void* AllocTo_p = (AllocTo_sz == 0) ? 0 : malloc (AllocTo_sz); \
  CopyTo( a, AllocTo_p ); \
} while (0)

/** Dynamic allocation. Not sure if useful.**/
#define Dynalloc(a, old_sz, new_sz) do \
{ \
  const size_t Dynalloc_old_sz = (old_sz)*sizeof(*a); \
  const size_t Dynalloc_new_sz = (new_sz)*sizeof(*a); \
  if (Dynalloc_new_sz > 0) { \
    void* Dynalloc_p = realloc (Dynalloc_old_sz == 0 ? 0 : (a), \
        Dynalloc_new_sz); \
    CopyTo( a, Dynalloc_p ); \
  } \
  else { \
    if (Dynalloc_old_sz > 0 && (a)) { \
      free (a); \
    } \
    a = 0; \
  } \
} while (0)

/** Duplicate {b} to {a}.**/
#define Duplic( a, b, n )  do \
{ \
  const size_t Duplic_sz = (n) * sizeof(*b); \
  void* Duplic_p = 0; \
  if (Duplic_sz > 0) \
  if ((Duplic_p = malloc (Duplic_sz))) \
  memcpy (Duplic_p, b, Duplic_sz); \
  CopyTo( a, Duplic_p ); \
} while (0)

/** Duplicate memory.
 * \param T  Type.
 * \param a  Source block.
 * \param n  Number of elements to duplicate.
 * \return  NULL when the number of elements is zero.
 **/
#define DupliT( T, a, n ) \
  ((n) == 0 ? (T*) 0 : \
   (T*) memcpy (malloc ((n) * sizeof (T)), a, (n) * sizeof (T)))

/** Declare a variable pointing to heap-allocated memory.
 * \param T  Type.
 * \param a  Variable name.
 * \param n  Number of elements to duplicate.
 * \sa AllocT()
 **/
#define DeclAlloc( T, a, n ) \
  T* const restrict a = AllocT( T, n )

/** Swap two values.**/
#define Swap2( a, b ) \
  do { \
    byte Swap2_tmp[sizeof(a)]; \
    memcpy(&tmp, &(a), sizeof(tmp)); \
    memcpy(&(a), &(b), sizeof(tmp)); \
    memcpy(&(b), &(tmp), sizeof(tmp)); \
  } while (0)

/** Swap two values.**/
#define SwapT( T, a, b ) \
  do { \
    const T SwapT_tmp = a; \
    a = b; \
    b = SwapT_tmp; \
  } while (0)


/** Explicitly convert true to 1 and false to 0.**/
#define OneIf( expr )  (!(expr) ? 0 : 1)

#ifndef __OPENCL_VERSION__
typedef struct PosetCmp PosetCmp;
struct PosetCmp
{
  ptrdiff_t off;
  PosetCmpFn fn;
};

qual_inline
  PosetCmp
dflt2_PosetCmp (ptrdiff_t off, PosetCmpFn fn)
{
  PosetCmp cmp;
  cmp.off = off;
  cmp.fn = fn;
  return cmp;
}

qual_inline
  PosetCmp
dflt3_PosetCmp (ptrdiff_t node_offset, ptrdiff_t key_offset, PosetCmpFn fn)
{
  return dflt2_PosetCmp (key_offset - node_offset, fn);
}

qual_inline
  sign_t
poset_cmp (PosetCmp cmp, const void* a, const void* b)
{
  return cmp.fn ((const void*) (cmp.off + (ptrdiff_t)a),
      (const void*) (cmp.off + (ptrdiff_t)b));
}

qual_inline
  sign_t
poset_cmp_lhs (PosetCmp cmp, const void* a, const void* b)
{
  return cmp.fn (a, (const void*) (cmp.off + (ptrdiff_t)b));
}

#define sign_of(x)  ((x) < 0 ? -1 : (x) > 0 ? 1 : 0)

/** Implemented in syscx.c **/
#define Default_RandomMod(n)  randommod_sysCx (n)
#define Default_Randomize(x)  randomize_sysCx (&(x), sizeof(x))

#define RandomMod(n)  Default_RandomMod(n)
#define Randomize(x)  Default_Randomize(x)

#define Zeroize(x)  memset(&(x), 0, sizeof(x))

/** Use this as a pointer to zero values without having to allocate memory.
 *
 * Don't write to this memory. It will segfault on some systems.
 **/
static const size_t Static00[] = {0,0};

/** Assign {a} as {0} iff they are not already equal.**/
#define Ensure0( a )  do { if (a)  a = 0; } while (0)

/** Implemented in syscx.c **/
void
dbglog_printf3 (const char* file,
    const char* func,
    uint line,
    const char* fmt,
    ...);

#define DBog1(s,a)  dbglog_printf3 (__FILE__,__FUNC__,__LINE__,s,a)
#define DBog2(s,a,b)  dbglog_printf3 (__FILE__,__FUNC__,__LINE__,s,a,b)
#define DBog3(s,a,b,c)  dbglog_printf3 (__FILE__,__FUNC__,__LINE__,s,a,b,c)
#define DBog4(s,a,b,c,d)  dbglog_printf3 (__FILE__,__FUNC__,__LINE__,s,a,b,c,d)
#define DBog5(s,a,b,c,d,e)  dbglog_printf3 (__FILE__,__FUNC__,__LINE__,s,a,b,c,d,e)
#define DBog0(s)  DBog1("%s",s)
#define DBog_zuint(x)  DBog2( "%s:%zu", #x, (zuint)(x) )
#define DBog_ujint(x)  DBog2( "%s:%lu", #x, (luint)(x) )
#define DBog_luint(x)  DBog2( "%s:%lu", #x, (luint)(x) )

#define BailOut( ret, msg ) \
  do \
{ \
  DBog0(msg); \
  return (ret); \
} while (0)

void
failout_sysCx (const char* msg);
#endif

#if !defined(NDEBUG)
#define Given( x )  assert(x)
#define Claim( x )  assert(x)
#elif defined(TestClaim)
#define Claim( x )  do \
{ \
  if (!(x)) \
  { \
    DBog1( "%s failed.", #x ); \
    failout_sysCx (""); \
  } \
} while (0)
#define Given( x )  Claim(x)
#else  /*v defined(NDEBUG) v*/
#ifdef _MSC_VER
# define assume(x) __assume(x)
#else
# define assume(x) do { if (!(x)) __builtin_unreachable(); } while (0)
#endif
#define Given( x )  assume(x)
#define Claim( x )  assert(x)
#endif

#define Claim2( a ,op, b )  Claim((a) op (b))

#define Claim2_uint( a, op, b ) \
  do { \
    if (!((a) op (b))) { \
      DBog5( "FAILED: (%s) where (%s == %u) and (%s == %u)", Stringify((a) op (b)), #a, (uint) (a), #b, (uint) (b) ); \
    } \
  } while (0)

#define skip_unless( cond )  if (!(cond))  continue

#define DeclLegit(good) sign_t good = 1; sign_t* const DoLegit_vbl = &good

#define DoLegit3(p, good, msg) \
  for (good = good ? -1 : 0; \
      good < 0; \
      good = !!(p) ? 1 : (msg ? (DBog0(msg), 0) : (assert(0), 0)))

#define DoLegit2(good,msg)  DoLegit3( good, good, msg )
#define DoLegitP(p,msg)  DoLegit3( p, *DoLegit_vbl, msg )
#define DoLegit1(msg)  DoLegitP( *DoLegit_vbl, msg )
#define DoLegit(msg)  DoLegit1( msg )
#define DoLegitLine(msg)  DoLegit1( msg )  *DoLegit_vbl =
#define DoLegitLineP(p,msg)  DoLegitP( p, msg )  p =

