/**
 * \file table.h
 * Dynamic array.
 **/
#ifndef Table_H_
#define Table_H_
#ifndef __OPENCL_VERSION__
#include "def.h"

#include <stdlib.h>
#include <string.h>
#endif  /* #ifndef __OPENCL_VERSION__ */

typedef unsigned int TableElSz;

#define TableT( S )  TableT_##S
#define TableElT( S )  TableElT_##S

typedef struct Table Table;
struct Table
{
  void* s;
  zuint sz;
  TableElSz elsz;
  bitint alloc_lgsz;
};

typedef struct ConstTable ConstTable;
struct ConstTable
{
  const void* s;
  zuint sz;
  TableElSz elsz;
  bitint alloc_lgsz;
};

#define DeclTableT( S, T ) \
  typedef struct TableT_##S TableT_##S; \
  typedef T TableElT_##S; \
  struct TableT_##S { \
    TableElT_##S* s; \
    zuint sz; \
    bitint alloc_lgsz; \
  }

#define FixTableT( S, N ) \
  struct { \
    TableElT_##S s[N]; \
    zuint sz; \
    bitint alloc_lgsz; \
  }

#define DeclTableT_MemLoc
DeclTableT( MemLoc, void* );
#define DeclTableT_byte
DeclTableT( byte, byte );
#define DeclTableT_char
DeclTableT( char, char );
#define DeclTableT_cstr
DeclTableT( cstr, char* );
#define DeclTableT_const_cstr
DeclTableT( const_cstr, const char* );
#define DeclTableT_int
DeclTableT( int, int );
#define DeclTableT_uint
DeclTableT( uint, uint );
#define DeclTableT_zuint
DeclTableT( zuint, zuint );
#define DeclTableT_luint
DeclTableT( luint, luint );
#define DeclTableT_ujint
DeclTableT( ujint, ujint );
#define DeclTableT_uint2
DeclTableT( uint2, uint2 );
#define DeclTableT_ujint2
DeclTableT( ujint2, ujint2 );

#define DeclTableT_TableT_uint
DeclTableT( TableT_uint, TableT(uint) );

qual_inline
  Table
dflt4_Table (void* s, zuint sz, TableElSz elsz, bitint alloc_lgsz)
{
  Table t;
  t.s = s;
  t.sz = sz;
  t.elsz = elsz;
  t.alloc_lgsz = alloc_lgsz;
  return t;
}
qual_inline
  Table
dflt1_Table (TableElSz elsz)
{
  return dflt4_Table (0, 0, elsz, 0);
}
#define DEFAULT_Table  { 0, 0, 0 }
#define DEFAULT_Z_Table( S )  { (S*)Static00, 1, 0 }

#define DeclTable( S, table )  TableT_##S table = DEFAULT_Table
#define DeclZTable( S, table ) TableT_##S table = DEFAULT_Z_Table(S)

#define MakeCastTable( t ) \
  dflt4_Table ((t).s, (t).sz, sizeof(*(t).s), (t).alloc_lgsz)

qual_inline
  ConstTable
dflt4_ConstTable (const void* s, zuint sz,
    TableElSz elsz, bitint alloc_lgsz)
{
  ConstTable t;
  t.s = s;
  t.sz = sz;
  t.elsz = elsz;
  t.alloc_lgsz = alloc_lgsz;
  return t;
}
#define MakeCastConstTable( t ) \
  dflt4_ConstTable ((t).s, (t).sz, sizeof(*(t).s), (t).alloc_lgsz)

#define XferCastTable( t, name )  do \
{ \
  memcpy (&(t).s, &(name).s, sizeof(void*)); \
  BSfx( t ,=, name ,.sz ); \
  BSfx( t ,=, name ,.alloc_lgsz ); \
} while (0)


qual_inline
  void
init1_Table (Table* t, TableElSz elsz)
{
  *t = dflt1_Table (elsz);
}
#define InitTable( t )  do \
{ \
  (t).s = 0; \
  (t).sz = 0; \
  (t).alloc_lgsz = 0; \
} while (0)


/** Make table of size 1 starting with a null value.
 * Make sure that you don't write to this and that
 * the element size is not larger than a pointer.
 **/
qual_inline
  void
init_z_Table (Table* t, TableElSz elsz)
{
  init1_Table (t, elsz);
  t->s = (void*) Static00;
  t->sz = 1;
}
#define InitZTable( t )  do \
{ \
  (t).alloc_lgsz = 0; \
  *((byte**) &(t).s) = (byte*) Static00; \
  (t).sz = 1; \
} while (0)

#define InitFixTable( t )  do \
{ \
  (t).sz = 0; \
  (t).alloc_lgsz = BITINT_MAX; \
} while (0)

#ifndef __OPENCL_VERSION__
qual_inline
  void
lose_Table (Table* t)
{
  if (t->alloc_lgsz > 0 && t->alloc_lgsz != BITINT_MAX)
    free (t->s);
}
#define LoseTable( t )  do \
{ \
  Table LoseTable_t = MakeCastTable( t ); \
  lose_Table (&LoseTable_t); \
} while (0)
#endif  /* #ifndef __OPENCL_VERSION__ */

#define AllocszTable( t ) \
  ((t).alloc_lgsz == 0 ? 0 : (zuint)1 << ((t).alloc_lgsz - 1))
qual_inline
  zuint
allocsz_Table (const Table* t)
{
  return AllocszTable( *t );
}

qual_inline
  void*
elt_Table (Table* t, zuint idx)
{
  return EltZ( t->s, idx, t->elsz );
}
#define DeclEltTable( S, x, t, idx ) \
  TableElT_##S* const x = Elt( (t).s, idx )

qual_inline
  zuint
idxelt_Table (const Table* t, const void* el)
{
  return (zuint) IdxEltZ( t->s, el, t->elsz );
}
#define IdxEltTable( t, el ) \
  (zuint) IdxEltZ( (t).s, el, sizeof(*(t).s) )


#ifndef __OPENCL_VERSION__
qual_inline
  void
grow_Table (Table* t, zuint capac)
{
  grow_LaceA_(&t->s, &t->sz, &t->alloc_lgsz, t->elsz,
              capac, realloc);
}
#define GrowTable( t, capac ) \
  grow_LaceA_((void**)&(t).s, &(t).sz, &(t).alloc_lgsz, sizeof(*(t).s), capac, \
              realloc)

qual_inline
  void
mpop_Table (Table* t, zuint capac)
{
  mpop_LaceA_(&t->s, &t->sz, &t->alloc_lgsz, t->elsz,
              capac, realloc);
}
#define MPopTable( t, capac ) \
  mpop_LaceA_((void**)&(t).s, &(t).sz, &(t).alloc_lgsz, sizeof(*(t).s), capac, \
              realloc)
#endif  /* #ifndef __OPENCL_VERSION__ */


/**! Pop table without deallocation.**/
qual_inline
  void
cpop_Table (Table* t, zuint n)
{
  t->sz -= n;
}
#define CPopTable( a, n )  do \
{ \
  (a).sz -= (n); \
} while (0)


qual_inline
  void*
top_Table (Table* t)
{
  return elt_Table (t, t->sz - 1);
}
#define TopTable( t )  Elt((t).s, (t).sz-1)

qual_inline
  bool
elt_in_Table (Table* t, void* el)
{
  return EltInZ( t->s, el, t->sz, t->elsz );
}
#define EltInTable( t, el ) \
  EltInZ( (t).s, (el), (t).sz, sizeof(*(t).s) )

#ifndef __OPENCL_VERSION__
qual_inline
  void*
grow1_Table (Table* t)
{
  return grow_LaceA_(&t->s, &t->sz, &t->alloc_lgsz, t->elsz,
                     1, realloc);
}

#define Grow1Table( t ) \
  (grow_LaceA_((void**)&(t).s, &(t).sz, &(t).alloc_lgsz, \
               sizeof(*(t).s), 1, realloc), \
   TopTable( t ))
#define DeclGrow1Table( S, x, t ) \
  TableElT_##S* const x = Grow1Table( t )
#define PushTable( table, x ) \
  *(Grow1Table( table )) = (x)


qual_inline
  void
resize_Table (Table* t, zuint capac)
{
  if (t->sz <= capac)  grow_Table (t, capac - t->sz);
  else                 mpop_Table (t, t->sz - capac);
}
#define ResizeTable( t, capac )  do \
{ \
  Table ReizeTable_t = MakeCastTable( t ); \
  resize_Table (&ReizeTable_t, capac); \
  XferCastTable( t, ReizeTable_t ); \
} while (0)

qual_inline
  void
size_Table (Table* t, zuint capac)
{ resize_Table (t, capac); }
#define SizeTable( t, capac )  ResizeTable(t, capac)

/** Never downsize.**/
qual_inline
  void
ensize_Table (Table* t, zuint capac)
{
  if (t->sz < capac)
    grow_Table (t, capac - t->sz);
  else
    t->sz = capac;
}
#define EnsizeTable( t, capac )  do \
{ \
  Table EnsizeTable_t = MakeCastTable( t ); \
  ensize_Table (&EnsizeTable_t, capac); \
  XferCastTable( t, EnsizeTable_t ); \
} while (0)


qual_inline
  void
pack_Table (Table* t)
{
  if (t->alloc_lgsz > 0 &&
      (t->sz << 1) < ((zuint) 1 << t->alloc_lgsz))
  {
    if (t->sz == 0)
    {
      free (t->s);
      t->s = 0;
      t->alloc_lgsz = 0;
    }
    else
    {
      t->s = realloc (t->s, t->sz * t->elsz);
      while ((t->sz << 1) < ((zuint) 1 << t->alloc_lgsz))
        t->alloc_lgsz -= 1;
    }
  }
}
#define PackTable( t )  do \
{ \
  Table PackTable_t = MakeCastTable( t ); \
  pack_Table (&PackTable_t); \
  XferCastTable( t, PackTable_t ); \
} while (0)

qual_inline
  void
affy_Table (Table* t, zuint capac)
{
  if (t->alloc_lgsz > 0) {
    t->s = realloc (t->s, t->elsz * capac);
    t->alloc_lgsz = SIZE_BIT - 1;
  }
  else if (t->sz < capac) {
    const void* s = t->s;
    t->s = malloc (t->elsz * capac);
    if (t->sz > 0)
      memcpy (t->s, s, t->elsz * t->sz);
    t->alloc_lgsz = SIZE_BIT - 1;
  }
}
#define AffyTable( t, capac )  do \
{ \
  Table AffyTable_t = MakeCastTable( t ); \
  affy_Table (&AffyTable_t, capac); \
  XferCastTable( t, AffyTable_t ); \
} while (0)

qual_inline
  void
affysz_Table (Table* t, zuint sz)
{
  affy_Table (t, sz);
  t->sz = sz;
}

qual_inline
  void
copy_Table (Table* a, const Table* b)
{
  if (a->elsz != b->elsz)
  {
    a->sz = a->sz * a->elsz / b->elsz;
    a->elsz = b->elsz;
  }

  ensize_Table (a, b->sz);
  memcpy (a->s, b->s, a->sz * a->elsz);
}

qual_inline
  void
copy_const_Table (Table* a, const ConstTable* b)
{
  if (a->elsz != b->elsz)
  {
    a->sz = a->sz * a->elsz / b->elsz;
    a->elsz = b->elsz;
  }

  ensize_Table (a, b->sz);
  memcpy (a->s, b->s, a->sz * a->elsz);
}
#define CopyTable( a, b )  do \
{ \
  Table CopyTable_a = MakeCastTable( a ); \
  const ConstTable CopyTable_b = MakeCastConstTable( b ); \
  copy_const_Table (&CopyTable_a, &CopyTable_b); \
  XferCastTable( a, CopyTable_a ); \
} while (0)

qual_inline
  void
cat_Table (Table* a, const Table* b)
{
  zuint off = a->sz;
  if (b->sz == 0)  return;
  grow_Table (a, b->sz);
  Claim( a->elsz == b->elsz );
  memcpy (elt_Table (a, off), b->s, a->elsz * b->sz);
}

qual_inline
  void
cat_const_Table (Table* a, const ConstTable* b)
{
  zuint off = a->sz;
  if (b->sz == 0)  return;
  grow_Table (a, b->sz);
  Claim( a->elsz == b->elsz );
  memcpy (elt_Table (a, off), b->s, a->elsz * b->sz);
}
#define CatTable( a, b )  do \
{ \
  Table CatTable_a = MakeCastTable( a ); \
  const ConstTable CatTable_b = MakeCastConstTable( b ); \
  cat_const_Table (&CatTable_a, &CatTable_b); \
  XferCastTable( a, CatTable_a ); \
} while (0)


/** Clear the table and free most of its memory.**/
qual_inline
  void
clear_Table (Table* a)
{ mpop_Table (a, a->sz); }
#define ClearTable( a )  MPopTable( a, (a).sz )

qual_inline
  void
flush_Table (Table* a)
{
  a->sz = 0;
}
#define FlushTable( a )  do \
{ \
  (a).sz = 0; \
} while (0)
#endif  /* #ifndef __OPENCL_VERSION__ */

qual_inline
  void
state_of_index (uint* state, zuint idx, const uint* doms, uint n)
{
  uint i;
  for (i = n; i > 0; --i) {
    state[i-1] = idx % doms[i-1];
    idx /= doms[i-1];
  }
}

qual_inline
  zuint
index_of_state (const uint* state, const uint* doms, uint n)
{
  zuint idx = 0;
  uint i;
  for (i = 0; i < n; ++i) {
    idx *= doms[i];
    idx += state[i];
  }
  return idx;
}

#endif

