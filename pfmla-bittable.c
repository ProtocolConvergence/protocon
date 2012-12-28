
#include "pfmla-bittable.h"

typedef struct BitTablePFmlaCtx BitTablePFmlaCtx;

struct BitTablePFmlaCtx
{
  PFmlaCtx fmlactx;
};


static
  void
op2_BitTablePFmla (PFmlaCtx* fmlactx, BitTable** c, BitOp op, const BitTable* a, const BitTable* b)
{
  BitTable tmp;
  (void) fmlactx;
  if (!*c)
  {
    *c = AllocT( BitTable, 1 );
    **c = dflt_BitTable ();
  }
  if (!a)
  {
    tmp = dflt_BitTable ();
    tmp.sz = b->sz;
    a = &tmp;
  }
  else if (!b)
  {
    tmp = dflt_BitTable ();
    tmp.sz = a->sz;
    b = &tmp;
  }
  op2_BitTable (*c, op, *a, *b);
}

static
  bool
tautology_ck_BitTablePFmla (PFmlaCtx* fmlactx, const BitTable* a)
{
  (void) fmlactx;
  return all_BitTable (*a) ? true : false;
}

static
  void
lose_BitTablePFmla (PFmlaCtx* fmlactx, BitTable* a)
{
  (void) fmlactx;
  lose_BitTable (a);
  free (a);
}

static
  void
commit_initialization_BitTablePFmlaCtx (PFmlaCtx* fmlactx)
{
  (void) fmlactx;
}

static
  void*
lose_BitTablePFmlaCtx (PFmlaCtx* fmlactx)
{
  BitTablePFmlaCtx* ctx = CastUp( BitTablePFmlaCtx, fmlactx, fmlactx );
  return ctx;
}

  PFmlaCtx*
make_BitTablePFmla ()
{
  static bool vt_initialized = false;
  static PFmlaOpVT vt;
  BitTablePFmlaCtx* ctx = AllocT( BitTablePFmlaCtx, 1 );
  if (!vt_initialized)
  {
    vt_initialized = true;
    memset (&vt, 0, sizeof (vt));
    vt.op2_fn = (void (*) (PFmlaCtx*, void**, BitOp, const void*, const void*))        op2_BitTablePFmla;
    //vt.exist_set_fn    = (void (*) (PFmlaCtx*, void**, const void*, uint))          exist_set_BitTablePFmla;
    //vt.subst_set_fn    = (void (*) (PFmlaCtx*, void**, const void*, uint, uint))    subst_set_BitTablePFmla;
    vt.tautology_ck_fn = (bool (*) (PFmlaCtx*, const void*))                     tautology_ck_BitTablePFmla;
    vt.lose_fn         = (void (*) (PFmlaCtx*, void*))                                   lose_BitTablePFmla;
    //vt.vbl_eql_fn      = (void (*) (PFmlaCtx*, void**, uint, uint))                   vbl_eql_BitTablePFmla;
    //vt.vbl_eqlc_fn     = (void (*) (PFmlaCtx*, void**, uint, uint))                  vbl_eqlc_BitTablePFmla;
    vt.ctx_commit_initialization_fn = commit_initialization_BitTablePFmlaCtx;
    vt.ctx_lose_fn = lose_BitTablePFmlaCtx;
  }
  init1_PFmlaCtx (&ctx->fmlactx, &vt);
  return &ctx->fmlactx;
}

