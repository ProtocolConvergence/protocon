
#include "sesp.h"
#include "alphatab.h"

static
  Sign
cmp_MemLoc (const void* a, const void* b)
{
  if ((size_t) a < (size_t) b) {
    return -1;
  }
  if ((size_t) a == (size_t) b) {
    return 0;
  }
  return 1;
}

  SespCtx*
make_SespCtx ()
{
  SespCtx* ctx = AllocT( SespCtx, 1 );
  InitAssocia( SespVT*, SespKind*, ctx->kindmap, cmp_MemLoc );
  ctx->nil.base.kind = 0;
  ctx->nil.car = 0;
  ctx->nil.cdr = 0;
  return ctx;
}

  void
free_SespCtx (SespCtx* ctx)
{

  for (Assoc* assoc = beg_Associa (&ctx->kindmap);
       assoc;
       assoc = next_Assoc (assoc))
  {
    SespKind* kind = *(SespKind**) val_of_Assoc (&ctx->kindmap, assoc);
    free_SespKind (kind);
  }
  lose_Associa (&ctx->kindmap);
  free (ctx);
}

  SespCtx*
ctx_of_Sesp (const Sesp a)
{
  if (!a->kind)
    return CastUp( SespCtx, nil, a );
  return a->kind->ctx;
}

  SespKind*
ensure_kind_SespCtx (SespCtx* ctx, const SespVT* vt)
{
  bool added = false;
  Assoc* assoc =
    ensure1_Associa (&ctx->kindmap, vt, &added);
  if (added) {
    SespKind* kind = make_SespKind (vt);
    kind->ctx = ctx;
    val_fo_Assoc (&ctx->kindmap, assoc, &kind);
  }
  return *(SespKind**) val_of_Assoc (&ctx->kindmap, assoc);
}

/** Easy make function for SespKind.*/
  SespKind*
make_SespKind (const SespVT* vt)
{
  SespKind* kind = AllocT( SespKind, 1 );
  kind->cells = dflt1_LgTable (vt->size);
  kind->vt = vt;
  return kind;
}

  Sesp
take_SespKind (SespKind* kind)
{
  void* el = take_LgTable (&kind->cells);
  Sesp sp = CastOff( SespBase, el ,+, kind->vt->base_offset );
  sp->kind = kind;
  return sp;
}

  void
free_SespKind (SespKind* kind)
{
  for (zuint i = begidx_LgTable (&kind->cells);
       i != SIZE_MAX;
       i = nextidx_LgTable (&kind->cells, i))
  {
    void* el = elt_LgTable (&kind->cells, i);
    Sesp sp = CastOff( SespBase, el ,+, kind->vt->base_offset );
    lose_Sesp (sp);
  }
  lose_LgTable (&kind->cells);

  free (kind);
}

  SespCell
cons_Sesp (Sesp car, SespCell cdr)
{
  SespCtx* ctx = ctx_of_Sesp (car);
  SespKind* kind = ensure_kind_SespCtx (ctx, vt_SespCell ());
  Sesp base = take_SespKind (kind);
  SespCell cons = CastUp( SespCellBase, base, base );

  Claim2( ctx ,==, ctx_of_Sesp (&cdr->base) );

  cons->car = car;
  cons->cdr = cdr;
  return cons;
}

  Sesp
list1_Sesp (Sesp a)
{
  SespCtx* ctx = ctx_of_Sesp (a);
  SespCell cons = &ctx->nil;
  cons = cons_Sesp (a, cons);
  return &cons->base;
}

  Sesp
list2_Sesp (Sesp a, Sesp b)
{
  SespCtx* ctx = ctx_of_Sesp (a);
  SespCell cons = &ctx->nil;
  cons = cons_Sesp (a, cons_Sesp (b, cons));
  return &cons->base;
}

  Sesp
list3_Sesp (Sesp a, Sesp b, Sesp c)
{
  SespCtx* ctx = ctx_of_Sesp (a);
  SespCell cons = &ctx->nil;
  cons = cons_Sesp (c, cons);
  cons = cons_Sesp (b, cons);
  cons = cons_Sesp (a, cons);
  return &cons->base;
}

  Sesp
list4_Sesp (Sesp a, Sesp b, Sesp c, Sesp d)
{
  SespCtx* ctx = ctx_of_Sesp (a);
  SespCell cons = &ctx->nil;
  cons = cons_Sesp (d, cons);
  cons = cons_Sesp (c, cons);
  cons = cons_Sesp (b, cons);
  cons = cons_Sesp (a, cons);
  return &cons->base;
}

  bool
pushlast_Sesp (Sesp list, Sesp a)
{
  Sesp b = cdr_of_Sesp (list);
  if (nil_ck_Sesp (list))  return false;
  if (!list_ck_Sesp (list))  return false;
  while (!nil_ck_Sesp (b))
  {
    list = b;
    b = cdr_of_Sesp (list);
  }
  return cdr_fo_Sesp (list, list1_Sesp (a));
}

  const SespVT*
vt_SespCell ()
{
  static bool vt_initialized = false;
  static SespVT vt;
  if (!vt_initialized) {
    vt_initialized = true;
    vt.kind_name = "Cell";
    memset (&vt, 0, sizeof (vt));
    vt.base_offset = offsetof( SespCellBase, base );
    vt.size = sizeof(SespCellBase);
  }
  return &vt;
}

  SespCStr
make_SespCStr (SespCtx* ctx, const char* s)
{
  SespKind* kind = ensure_kind_SespCtx (ctx, vt_SespCStr ());
  SespCStr sp = to_SespCStr (take_SespKind (kind));
  sp->s = dup_cstr (s);
  return sp;
}

static void lose_SespCStr (Sesp base)
{
  SespCStr sp = to_SespCStr (base);
  free (sp->s);
}

static
  const char*
ccstr_of_SespCStr (const Sesp base)
{
  return to_SespCStr (base) -> s;
}

  const SespVT*
vt_SespCStr ()
{
  static bool vt_initialized = false;
  static SespVT vt;
  if (!vt_initialized) {
    vt_initialized = true;
    vt.kind_name = "CStr";
    memset (&vt, 0, sizeof (vt));
    vt.base_offset = offsetof( SespCStrBase, base );
    vt.size = sizeof(SespCStrBase);
    vt.lose_fn = lose_SespCStr;
    vt.ccstr_fn = ccstr_of_SespCStr;
  }
  return &vt;
}

  SespCCStr
make_SespCCStr (SespCtx* ctx, const char* s)
{
  SespKind* kind = ensure_kind_SespCtx (ctx, vt_SespCCStr ());
  SespCCStr sp = to_SespCCStr (take_SespKind (kind));
  sp->s = s;
  return sp;
}

static
  const char*
ccstr_of_SespCCStr (const Sesp base)
{
  return to_SespCCStr (base) -> s;
}

  const SespVT*
vt_SespCCStr ()
{
  static bool vt_initialized = false;
  static SespVT vt;
  if (!vt_initialized) {
    vt_initialized = true;
    vt.kind_name = "CCstr";
    memset (&vt, 0, sizeof (vt));
    vt.base_offset = offsetof( SespCCStrBase, base );
    vt.size = sizeof(SespCCStrBase);
    vt.ccstr_fn = ccstr_of_SespCCStr;
  }
  return &vt;
}

  SespNat
make_SespNat (SespCtx* ctx, uint u)
{
  SespKind* kind = ensure_kind_SespCtx (ctx, vt_SespNat ());
  SespNat sp = to_SespNat (take_SespKind (kind));
  sp->u = u;
  return sp;
}

  const SespVT*
vt_SespNat ()
{
  static bool vt_initialized = false;
  static SespVT vt;
  if (!vt_initialized) {
    vt_initialized = true;
    vt.kind_name = "Nat";
    memset (&vt, 0, sizeof (vt));
    vt.base_offset = offsetof( SespNatBase, base );
    vt.size = sizeof(SespNatBase);
  }
  return &vt;
}

  SespInt
make_SespInt (SespCtx* ctx, int i)
{
  SespKind* kind = ensure_kind_SespCtx (ctx, vt_SespInt ());
  SespInt sp = to_SespInt (take_SespKind (kind));
  sp->i = i;
  return sp;
}

  const SespVT*
vt_SespInt ()
{
  static bool vt_initialized = false;
  static SespVT vt;
  if (!vt_initialized) {
    vt_initialized = true;
    vt.kind_name = "Int";
    memset (&vt, 0, sizeof (vt));
    vt.base_offset = offsetof( SespIntBase, base );
    vt.size = sizeof(SespIntBase);
  }
  return &vt;
}

