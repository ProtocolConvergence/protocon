/**
 * \file sesp.h
 * Base for S-expressions.
 **/
#ifndef Sesp_H_
#define Sesp_H_
#include <fildesh/fildesh.h>
#include "lgtable.h"

BEGIN_EXTERN_C

typedef struct SespBase SespBase;
typedef SespBase* Sesp;
typedef struct SespKind SespKind;
typedef struct SespCtx SespCtx;
typedef struct SespVT SespVT;
typedef struct SespCellBase SespCellBase;
typedef struct SespCStrBase SespCStrBase;
typedef struct SespCCStrBase SespCCStrBase;
typedef struct SespNatBase SespNatBase;
typedef struct SespIntBase SespIntBase;
typedef SespCellBase* SespCell;
typedef SespCStrBase* SespCStr;
typedef SespCCStrBase* SespCCStr;
typedef SespNatBase* SespNat;
typedef SespIntBase* SespInt;

struct SespBase
{
  SespKind* kind;
};

struct SespKind
{
  LgTable cells;
  const SespVT* vt;
  SespCtx* ctx;
};

struct SespCellBase
{
  SespBase base;
  Sesp car;
  SespCell cdr;
};

struct SespCtx
{
  SespCellBase nil;
  // SespVT -> SespKind*
  FildeshKV kindmap;
};

struct SespCCStrBase
{
  SespBase base;
  const char* s;
};

struct SespCStrBase
{
  SespBase base;
  char* s;
};

struct SespNatBase
{
  SespBase base;
  unsigned u;
};

struct SespIntBase
{
  SespBase base;
  int i;
};

struct SespVT
{
  const char* kind_name;
  size_t base_offset;
  size_t size;

  void (*lose_fn) (Sesp);

  const char* (*ccstr_fn) (const Sesp);
};

const SespVT* vt_SespCell ();
const SespVT* vt_SespCStr ();
const SespVT* vt_SespCCStr ();
const SespVT* vt_SespNat ();
const SespVT* vt_SespInt ();

SespCtx*
make_SespCtx ();
void
free_SespCtx (SespCtx* ctx);
SespCtx*
ctx_of_Sesp (const Sesp a);

SespKind*
ensure_kind_SespCtx (SespCtx* ctx, const SespVT* vt);

SespKind*
make_SespKind (const SespVT* vt);
void
free_SespKind (SespKind* kind);

SespCell
cons_Sesp (Sesp a, SespCell b);
Sesp
list1_Sesp (Sesp a);
Sesp
list2_Sesp (Sesp a, Sesp b);
Sesp
list3_Sesp (Sesp a, Sesp b, Sesp c);
Sesp
list4_Sesp (Sesp a, Sesp b, Sesp c, Sesp d);
bool
pushlast_Sesp (Sesp list, Sesp a);

static inline
  void
lose_Sesp (Sesp sp)
{
  if (sp->kind) {
    if (sp->kind->vt->lose_fn) {
      sp->kind->vt->lose_fn (sp);
    }
  }
}

static inline
  SespCell
to_SespCell (Sesp sp)
{
  return CastUp( SespCellBase, base, sp );
}

static inline
  SespCStr
to_SespCStr (Sesp sp)
{
  return CastUp( SespCStrBase, base, sp );
}

static inline
  SespCCStr
to_SespCCStr (Sesp sp)
{
  return CastUp( SespCCStrBase, base, sp );
}

static inline
  SespNat
to_SespNat (Sesp sp)
{
  return CastUp( SespNatBase, base, sp );
}

static inline
  SespInt
to_SespInt (Sesp sp)
{
  return CastUp( SespIntBase, base, sp );
}

static inline
  const char*
ccstr_of_Sesp (const Sesp a)
{
  if (a && a->kind && a->kind->vt->ccstr_fn) {
    return a->kind->vt->ccstr_fn (a);
  }
  return 0;
}

/** Check if this is an empty list.**/
static inline
  bool
nil_ck_Sesp (const Sesp a)
{
  return !a->kind;
}
/** Check if this is a list.**/
static inline
  bool
list_ck_Sesp (const Sesp a)
{
  if (nil_ck_Sesp (a))  return true;
  return (a->kind->vt == vt_SespCell ());
}
/** Check if this is not a list.**/
static inline
  bool
atom_ck_Sesp (const Sesp a)
{
  return !list_ck_Sesp (a);
}

static inline
  bool
uint_of_Sesp (const Sesp a, unsigned* x)
{
  if (a->kind && a->kind->vt == vt_SespNat ()) {
    *x = CastUp( SespNatBase, base, a ) -> u;
    return true;
  }
  return false;
}

static inline
  Sesp
car_of_Sesp (Sesp a)
{
  if (nil_ck_Sesp (a)) {
    return a;
  }
  if (list_ck_Sesp (a)) {
    SespCell cons = to_SespCell (a);
    return cons->car;
  }
  DBog0( "Called on an atom..." );
  return 0;
}

static inline
  Sesp
cdr_of_Sesp (Sesp a)
{
  if (nil_ck_Sesp (a)) {
    return a;
  }
  if (list_ck_Sesp (a)) {
    SespCell cons = to_SespCell (a);
    cons = cons->cdr;
    return &cons->base;
  }
  DBog0( "Called on an atom..." );
  return 0;
}

static inline
  Sesp
caar_of_Sesp (Sesp a)
{
  return car_of_Sesp (car_of_Sesp (a));
}

static inline
  Sesp
cadr_of_Sesp (Sesp a)
{
  return car_of_Sesp (cdr_of_Sesp (a));
}

static inline
  Sesp
cdar_of_Sesp (Sesp a)
{
  return cdr_of_Sesp (car_of_Sesp (a));
}

static inline
  Sesp
cddr_of_Sesp (Sesp a)
{
  return cdr_of_Sesp (cdr_of_Sesp (a));
}

static inline
  Sesp
caddr_of_Sesp (Sesp a)
{
  return car_of_Sesp (cddr_of_Sesp (a));
}

static inline
  Sesp
cddar_of_Sesp (Sesp a)
{
  return cdr_of_Sesp (cdar_of_Sesp (a));
}

static inline
  Sesp
cdddr_of_Sesp (Sesp a)
{
  return cdr_of_Sesp (cddr_of_Sesp (a));
}

static inline
  Sesp
caddar_of_Sesp (Sesp a)
{
  return car_of_Sesp (cddar_of_Sesp (a));
}

static inline
  Sesp
cadddr_of_Sesp (Sesp a)
{
  return car_of_Sesp (cdddr_of_Sesp (a));
}

static inline
  unsigned
sz_of_Sesp (Sesp a)
{
  unsigned n = 0;
  while (!nil_ck_Sesp (a)) {
    a = cdr_of_Sesp (a);
    n += 1;
  }
  return n;
}

static inline
  bool
car_fo_Sesp (Sesp a, Sesp b)
{
  SespCell a_cell;
  if (nil_ck_Sesp (a)) {
    DBog0( "Called on a Nil." );
    return false;
  }
  if (!list_ck_Sesp (a)) {
    DBog0( "Called on an atom!" );
    return false;
  }
  a_cell = to_SespCell (a);
  a_cell->car = b;
  return true;
}

static inline
  bool
cdr_fo_Sesp (Sesp a, Sesp b)
{
  SespCell a_cell = to_SespCell (a);
  if (nil_ck_Sesp (a)) {
    DBog0( "Called on a Nil." );
    return false;
  }
  if (!list_ck_Sesp (a)) {
    DBog0( "Called on an atom!" );
    return false;
  }
  if (!list_ck_Sesp (b)) {
    DBog0( "Can't replace cdr with non-list!" );
    return false;
  }
  a_cell->cdr = to_SespCell (b);
  return true;
}

SespCStr
make_SespCStr (SespCtx* ctx, const char* s);
SespCCStr
make_SespCCStr (SespCtx* ctx, const char* s);
SespNat
make_SespNat (SespCtx* ctx, unsigned u);
SespInt
make_SespInt (SespCtx* ctx, int i);

static inline
  Sesp
make_cstr_Sesp (SespCtx* ctx, const char* s)
{
  return &make_SespCStr (ctx, s)->base;
}

static inline
  Sesp
make_ccstr_Sesp (SespCtx* ctx, const char* s)
{
  return &make_SespCCStr (ctx, s)->base;
}

static inline
  Sesp
make_Nat_Sesp (SespCtx* ctx, unsigned u)
{
  return &make_SespNat (ctx, u)->base;
}

static inline
  Sesp
make_Int_Sesp (SespCtx* ctx, int i)
{
  return &make_SespInt (ctx, i)->base;
}

static inline
  Sesp
cons_ccstr_Sesp (const char* a, Sesp b)
{
  SespCell cell = cons_Sesp (make_ccstr_Sesp (ctx_of_Sesp (b), a), to_SespCell (b));
  return &cell->base;
}

static inline
  Sesp
list2_ccstr_Sesp (const char* a, Sesp b)
{
  return list2_Sesp (make_ccstr_Sesp (ctx_of_Sesp (b), a), b);
}

static inline
  Sesp
list3_ccstr_Sesp (const char* a, Sesp b, Sesp c)
{
  return list3_Sesp (make_ccstr_Sesp (ctx_of_Sesp (b), a), b, c);
}

static inline
  Sesp
list4_ccstr_Sesp (const char* a, Sesp b, Sesp c, Sesp d)
{
  return list4_Sesp (make_ccstr_Sesp (ctx_of_Sesp (b), a), b, c, d);
}

END_EXTERN_C
#endif
