
#include "pfmla-bittable.h"

typedef struct BitTablePFmla BitTablePFmla;
typedef struct BitTablePFmlaCtx BitTablePFmlaCtx;

struct BitTablePFmla
{
  PFmlaBase base;
  BitTable bt;
};

struct BitTablePFmlaCtx
{
  PFmlaCtx fmlactx;
};

static
  const BitTablePFmla*
ccastup_as_BitTablePFmla (const PFmla g)
{
  return CastUp( const BitTablePFmla, base, g );
}

static
  BitTablePFmla*
castup_as_BitTablePFmla (PFmla g)
{
  return CastUp( BitTablePFmla, base, g );
}

static
  BitTablePFmlaCtx*
castup_as_BitTablePFmlaCtx (PFmlaCtx* fmlactx)
{
  return CastUp( BitTablePFmlaCtx, fmlactx, fmlactx );
}


static
  void
op2_BitTablePFmla (PFmlaCtx* fmlactx, PFmla* base_c, BitOp op,
                   const PFmla base_a, const PFmla base_b)
{
  const BitTablePFmla* a = ccastup_as_BitTablePFmla (base_a);
  const BitTablePFmla* b = ccastup_as_BitTablePFmla (base_b);
  BitTablePFmla* c = castup_as_BitTablePFmla (*base_c);
  (void) fmlactx;
  op2_BitTable (&c->bt, op, a->bt, b->bt);
}

static
  bool
tautology_ck_BitTablePFmla (PFmlaCtx* fmlactx, const PFmla base_a)
{
  const BitTablePFmla* a = ccastup_as_BitTablePFmla (base_a);
  (void) fmlactx;
  return all_BitTable (a->bt) ? true : false;
}

static
  PFmla
make_BitTablePFmla (PFmlaCtx* fmlactx)
{
  BitTablePFmla* a = AllocT( BitTablePFmla, 1 );
  (void) fmlactx;
  a->bt = dflt_BitTable ();
  return &a->base;
}

static
  void
free_BitTablePFmla (PFmlaCtx* fmlactx, PFmla base_a)
{
  BitTablePFmla* a = castup_as_BitTablePFmla (base_a);
  (void) fmlactx;
  lose_BitTable (&a->bt);
  free (a);
}

static
  void*
lose_BitTablePFmlaCtx (PFmlaCtx* fmlactx)
{
  BitTablePFmlaCtx* ctx = castup_as_BitTablePFmlaCtx (fmlactx);
  return ctx;
}

  PFmlaCtx*
make_BitTablePFmlaCtx ()
{
  static bool vt_initialized = false;
  static PFmlaOpVT vt;
  BitTablePFmlaCtx* ctx = AllocT( BitTablePFmlaCtx, 1 );
  if (!vt_initialized)
  {
    vt_initialized = true;
    memset (&vt, 0, sizeof (vt));
    vt.op2_fn          =          op2_BitTablePFmla;
    //vt.exist_set_fn    =    exist_set_BitTablePFmla;
    //vt.subst_set_fn    =    subst_set_BitTablePFmla;
    vt.tautology_ck_fn = tautology_ck_BitTablePFmla;
    vt.make_fn         =         make_BitTablePFmla;
    vt.free_fn         =         free_BitTablePFmla;
    //vt.vbl_eql_fn      =      vbl_eql_BitTablePFmla;
    //vt.vbl_eqlc_fn     =     vbl_eqlc_BitTablePFmla;
    vt.ctx_lose_fn = lose_BitTablePFmlaCtx;
  }
  init1_PFmlaCtx (&ctx->fmlactx, &vt);
  return &ctx->fmlactx;
}

