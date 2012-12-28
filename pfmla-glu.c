
#include "pfmla-glu.h"

#define HAVE_ASSERT_H 1
#include "mdd.h"

typedef struct GluPFmlaCtx GluPFmlaCtx;

struct GluPFmlaCtx
{
  PFmlaCtx fmlactx;
  mdd_manager* ctx;
  array_t** vbl_lists;
};


static
  void
op2_GluPFmla (PFmlaCtx* ctx, mdd_t** c, BitOp op, mdd_t* a, mdd_t* b)
{
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
smooth_vbls_GluPFmla (PFmlaCtx* fmlactx, mdd_t** dst, mdd_t* src, uint set_id)
{
  GluPFmlaCtx* ctx = CastUp( GluPFmlaCtx, fmlactx, fmlactx );
  mdd_t* tmp = *dst;
  *dst = mdd_smooth (ctx->ctx, src, ctx->vbl_lists[set_id]);
  if (tmp)  mdd_free (tmp);
}

static
  void
subst_vbls_GluPFmla (PFmlaCtx* fmlactx, mdd_t** dst, mdd_t* src,
                     uint set_id_new, uint set_id_old)
{
  GluPFmlaCtx* ctx = CastUp( GluPFmlaCtx, fmlactx, fmlactx );
  mdd_t* tmp = *dst;
  *dst = mdd_substitute (ctx->ctx, src,
                         ctx->vbl_lists[set_id_old],
                         ctx->vbl_lists[set_id_new]);
  if (tmp)  mdd_free (tmp);
}

static
  bool
tautology_ck_GluPFmla (PFmlaCtx* ctx, mdd_t* a)
{
  (void) ctx;
  return mdd_is_tautology (a, 1) ? true : false;
}

static
  bool
unsat_ck_GluPFmla (PFmlaCtx* ctx, mdd_t* a)
{
  (void) ctx;
  return mdd_is_tautology (a, 0) ? true : false;
}

static
  bool
equiv_ck_GluPFmla (PFmlaCtx* ctx, mdd_t* a, mdd_t* b)
{
  (void) ctx;
  return mdd_equal (a, b) ? true : false;
}

static
  void
lose_GluPFmla (PFmlaCtx* ctx, mdd_t* a)
{
  (void) ctx;
  mdd_free (a);
}

static
  void
vbl_eql_GluPFmla (PFmlaCtx* fmlactx , mdd_t** dst, uint vbl_id_0, uint vbl_id_1)
{
  GluPFmlaCtx* ctx = CastUp( GluPFmlaCtx, fmlactx, fmlactx );
  if (*dst)  mdd_free (*dst);
  *dst = mdd_eq (ctx->ctx, vbl_id_0, vbl_id_1);
}

static
  void
vbl_eqlc_GluPFmla (PFmlaCtx* fmlactx, mdd_t** dst, uint vbl_id, uint x)
{
  GluPFmlaCtx* ctx = CastUp( GluPFmlaCtx, fmlactx, fmlactx );
  if (*dst)  mdd_free (*dst);
  *dst = mdd_eq_c (ctx->ctx, vbl_id, x);
}

static
  void
commit_initialization_GluPFmlaCtx (PFmlaCtx* fmlactx)
{
  GluPFmlaCtx* ctx = CastUp( GluPFmlaCtx, fmlactx, fmlactx );
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

  ctx->vbl_lists = AllocT( array_t*, fmlactx->vbl_lists.sz );
  {:for (i ; fmlactx->vbl_lists.sz)
    ctx->vbl_lists[i] = array_alloc(uint, 0);
    for (j ; fmlactx->vbl_lists.s[i].sz)
      array_insert_last(uint, ctx->vbl_lists[i], fmlactx->vbl_lists.s[i].s[j]);
  }
}

static
  void*
lose_GluPFmlaCtx (PFmlaCtx* fmlactx)
{
  GluPFmlaCtx* ctx = CastUp( GluPFmlaCtx, fmlactx, fmlactx );
  if (ctx->vbl_lists)
  {
    for (i ; fmlactx->vbl_lists.sz)
      array_free(ctx->vbl_lists[i]);
    free (ctx->vbl_lists);
  }
  if (ctx->ctx)
    mdd_quit (ctx->ctx);
  return ctx;
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
    vt.op2_fn = (void (*) (PFmlaCtx*, void**, BitOp, const void*, const void*))        op2_GluPFmla;
    vt.smooth_vbls_fn  = (void (*) (PFmlaCtx*, void**, const void*, uint))        smooth_vbls_GluPFmla;
    vt.subst_vbls_fn   = (void (*) (PFmlaCtx*, void**, const void*, uint, uint))   subst_vbls_GluPFmla;
    vt.tautology_ck_fn = (bool (*) (PFmlaCtx*, const void*))                     tautology_ck_GluPFmla;
    vt.unsat_ck_fn     = (bool (*) (PFmlaCtx*, const void*))                         unsat_ck_GluPFmla;
    vt.equiv_ck_fn     = (bool (*) (PFmlaCtx*, const void*, const void*))            equiv_ck_GluPFmla;
    vt.lose_fn         = (void (*) (PFmlaCtx*, void*))                                   lose_GluPFmla;
    vt.vbl_eql_fn      = (void (*) (PFmlaCtx*, void**, uint, uint))                   vbl_eql_GluPFmla;
    vt.vbl_eqlc_fn     = (void (*) (PFmlaCtx*, void**, uint, uint))                  vbl_eqlc_GluPFmla;
    vt.ctx_commit_initialization_fn = commit_initialization_GluPFmlaCtx;
    vt.ctx_lose_fn = lose_GluPFmlaCtx;
  }
  init1_PFmlaCtx (&ctx->fmlactx, &vt);
  ctx->ctx = 0;
  return &ctx->fmlactx;
}

