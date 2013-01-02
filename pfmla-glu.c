
#define HAVE_ASSERT_H 1
#include "mdd.h"

#include "pfmla-glu.h"

typedef struct GluPFmla GluPFmla;
typedef struct GluPFmlaCtx GluPFmlaCtx;
DeclTableT( array_t_memloc, array_t* );

struct GluPFmla
{
  PFmlaBase base;
  mdd_t* mdd;
};

struct GluPFmlaCtx
{
  PFmlaCtx fmlactx;
  mdd_manager* ctx;
  TableT(array_t_memloc) vbl_lists;
};

static
  const GluPFmla*
ccastup_as_GluPFmla (const PFmla g)
{
  return CastUp( const GluPFmla, base, g );
}

static
  GluPFmla*
castup_as_GluPFmla (PFmla g)
{
  return CastUp( GluPFmla, base, g );
}

static
  GluPFmlaCtx*
castup_as_GluPFmlaCtx (PFmlaCtx* fmlactx)
{
  return CastUp( GluPFmlaCtx, fmlactx, fmlactx );
}

static
  void
op2_GluPFmla (PFmlaCtx* ctx, PFmla* base_c, BitOp op,
              const PFmla base_a, const PFmla base_b)
{
  mdd_t* a = ccastup_as_GluPFmla (base_a) -> mdd;
  mdd_t* b = ccastup_as_GluPFmla (base_b) -> mdd;
  mdd_t** c = & castup_as_GluPFmla (*base_c) -> mdd;
  mdd_t* tmp = 0;
  (void) ctx;

  switch (op)
  {
  case BitOp_NOT1:
    tmp = mdd_not (b);
    break;
  case BitOp_NIMP:
    tmp = mdd_and (a, b, 1, 0);
    break;
  case BitOp_NOT0:
    tmp = mdd_not (a);
    break;
  case BitOp_AND:
    tmp = mdd_and (a, b, 1, 1);
    break;
  case BitOp_XNOR:
    tmp = mdd_xnor (a, b);
    break;
  case BitOp_IDEN1:
    tmp = mdd_dup (b);
    break;
  case BitOp_IDEN0:
    tmp = mdd_dup (a);
    break;
  case BitOp_OR:
    tmp = mdd_or (a, b, 1, 1);
    break;
  default:
    Claim( 0 );
    break;
  };

  if (*c)  mdd_free (*c);
  *c = tmp;
}

static
  void
smooth_vbls_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_b, const PFmla base_a, uint set_id)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  GluPFmla* b = castup_as_GluPFmla (*base_b);
  mdd_t* tmp = b->mdd;

  b->mdd = mdd_smooth (ctx->ctx, a->mdd, ctx->vbl_lists.s[set_id]);
  if (tmp)  mdd_free (tmp);
}

static
  void
subst_vbls_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_b, const PFmla base_a,
                     uint set_id_new, uint set_id_old)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  GluPFmla* b = castup_as_GluPFmla (*base_b);
  mdd_t* tmp = b->mdd;

  b->mdd = mdd_substitute (ctx->ctx, a->mdd,
                           ctx->vbl_lists.s[set_id_old],
                           ctx->vbl_lists.s[set_id_new]);
  if (tmp)  mdd_free (tmp);
}

static
  bool
tautology_ck_GluPFmla (PFmlaCtx* ctx, const PFmla base_a)
{
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  (void) ctx;
  return mdd_is_tautology (a->mdd, 1) ? true : false;
}

static
  bool
unsat_ck_GluPFmla (PFmlaCtx* ctx, const PFmla base_a)
{
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  (void) ctx;
  return mdd_is_tautology (a->mdd, 0) ? true : false;
}

static
  bool
equiv_ck_GluPFmla (PFmlaCtx* ctx, const PFmla base_a, const PFmla base_b)
{
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  const GluPFmla* b = ccastup_as_GluPFmla (base_b);
  (void) ctx;
  return mdd_equal (a->mdd, b->mdd) ? true : false;
}

static
  bool
overlap_ck_GluPFmla (PFmlaCtx* ctx, const PFmla base_a, const PFmla base_b)
{
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  const GluPFmla* b = ccastup_as_GluPFmla (base_b);
  (void) ctx;
  return mdd_lequal (a->mdd, b->mdd, 1, 0) ? false : true;
}

static
  bool
subseteq_ck_GluPFmla (PFmlaCtx* ctx, const PFmla base_a, const PFmla base_b)
{
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  const GluPFmla* b = ccastup_as_GluPFmla (base_b);
  (void) ctx;
  return mdd_lequal (a->mdd, b->mdd, 1, 1) ? true : false;
}

static
  PFmla
make_GluPFmla (PFmlaCtx* ctx)
{
  GluPFmla* a = AllocT( GluPFmla, 1 );
  (void) ctx;
  a->mdd = 0;
  return &a->base;
}

static
  void
free_GluPFmla (PFmlaCtx* ctx, PFmla base_a)
{
  GluPFmla* a = castup_as_GluPFmla (base_a);
  (void) ctx;
  if (a->mdd)
    mdd_free (a->mdd);
  free (a);
}

static
  void
vbl_eql_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst,
                  uint vbl_id_0, uint vbl_id_1)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  if (dst->mdd)  mdd_free (dst->mdd);
  dst->mdd = mdd_eq (ctx->ctx, vbl_id_0, vbl_id_1);
}

static
  void
vbl_eqlc_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, uint vbl_id, uint x)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  if (dst->mdd)  mdd_free (dst->mdd);
  dst->mdd = mdd_eq_c (ctx->ctx, vbl_id, x);
}

static
  void
commit_initialization_GluPFmlaCtx (PFmlaCtx* fmlactx)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  array_t* doms = array_alloc(uint, 0);
  array_t* names = array_alloc(char*, 0);
  {:for (i ; fmlactx->vbls.sz)
    PFmlaVbl* vbl = (PFmlaVbl*) elt_LgTable (&fmlactx->vbls, i);
    array_insert_last(uint, doms, vbl->domsz);
    array_insert_last(const char*, names, cstr_of_AlphaTab (&vbl->name));
  }
  ctx->ctx = mdd_init_empty();
  mdd_create_variables(ctx->ctx, doms, names, 0);
  array_free(doms);
  array_free(names);
}

static
  void*
lose_GluPFmlaCtx (PFmlaCtx* fmlactx)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  if (ctx->vbl_lists.sz > 0)
  {
    for (i ; ctx->vbl_lists.sz)
      array_free(ctx->vbl_lists.s[i]);
    LoseTable( ctx->vbl_lists );
  }
  if (ctx->ctx)
    mdd_quit (ctx->ctx);
  return ctx;
}

static
  uint
add_vbl_list_GluPFmlaCtx (PFmlaCtx* fmlactx)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  PushTable( ctx->vbl_lists, array_alloc(uint, 0) );
  return ctx->vbl_lists.sz - 1;
}

static
  void
add_to_vbl_list_GluPFmlaCtx (PFmlaCtx* fmlactx, uint listid, uint vblid)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  array_insert_last(uint, ctx->vbl_lists.s[listid], vblid);
}

  PFmlaCtx*
make_GluPFmlaCtx ()
{
  static bool vt_initialized = false;
  static PFmlaOpVT vt;
  GluPFmlaCtx* ctx = AllocT( GluPFmlaCtx, 1 );
  if (!vt_initialized)
  {
    vt_initialized = true;
    memset (&vt, 0, sizeof (vt));
    vt.op2_fn          =          op2_GluPFmla;
    vt.smooth_vbls_fn  =  smooth_vbls_GluPFmla;
    vt.subst_vbls_fn   =   subst_vbls_GluPFmla;
    vt.tautology_ck_fn = tautology_ck_GluPFmla;
    vt.unsat_ck_fn     =     unsat_ck_GluPFmla;
    vt.equiv_ck_fn     =     equiv_ck_GluPFmla;
    vt.overlap_ck_fn   =   overlap_ck_GluPFmla;
    vt.subseteq_ck_fn  =  subseteq_ck_GluPFmla;
    vt.make_fn         =         make_GluPFmla;
    vt.free_fn         =         free_GluPFmla;
    vt.vbl_eql_fn      =      vbl_eql_GluPFmla;
    vt.vbl_eqlc_fn     =     vbl_eqlc_GluPFmla;
    vt.ctx_commit_initialization_fn = commit_initialization_GluPFmlaCtx;
    vt.ctx_lose_fn = lose_GluPFmlaCtx;
    vt.ctx_add_vbl_list_fn = add_vbl_list_GluPFmlaCtx;
    vt.ctx_add_to_vbl_list_fn = add_to_vbl_list_GluPFmlaCtx;
  }
  init1_PFmlaCtx (&ctx->fmlactx, &vt);
  ctx->ctx = 0;
  InitTable( ctx->vbl_lists );
  return &ctx->fmlactx;
}

