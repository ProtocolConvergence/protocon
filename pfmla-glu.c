
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
  array_t* pre_vbl_list;
  array_t* img_vbl_list;
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
  uint
id_of_pre (uint id)
{
  return id * 2 + 1;
}

static
  uint
id_of_img (uint id)
{
  return id * 2;
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
  case BitOp_XOR:
    tmp = mdd_xor (a, b);
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
  void
pre_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, const PFmla base_a)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  mdd_t* tmp = dst->mdd;
  dst->mdd = mdd_smooth (ctx->ctx, a->mdd, ctx->img_vbl_list);
  if (tmp)  mdd_free (tmp);
}

static
  void
pre1_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, const PFmla base_a, const PFmla base_b)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  const GluPFmla* b = ccastup_as_GluPFmla (base_b);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  mdd_t* subst = mdd_substitute (ctx->ctx, b->mdd,
                                 ctx->pre_vbl_list,
                                 ctx->img_vbl_list);
  mdd_t* conj = mdd_and (a->mdd, subst, 1, 1);
  mdd_free (subst);
  if (dst->mdd)  mdd_free (dst->mdd);
  dst->mdd = mdd_smooth (ctx->ctx, conj, ctx->img_vbl_list);
  mdd_free (conj);
}

static
  void
img_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, const PFmla base_a)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  mdd_t* img = mdd_smooth (ctx->ctx, a->mdd, ctx->pre_vbl_list);
  if (dst->mdd)  mdd_free (dst->mdd);
  dst->mdd = mdd_substitute (ctx->ctx, img,
                             ctx->img_vbl_list,
                             ctx->pre_vbl_list);
  mdd_free (img);
}

static
  void
img1_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, const PFmla base_a, const PFmla base_b)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  const GluPFmla* b = ccastup_as_GluPFmla (base_b);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  mdd_t* rel = mdd_and (a->mdd, b->mdd, 1, 1);
  mdd_t* img = mdd_smooth (ctx->ctx, rel, ctx->pre_vbl_list);
  if (dst->mdd)  mdd_free (dst->mdd);
  mdd_free (rel);
  dst->mdd = mdd_substitute (ctx->ctx, img,
                             ctx->img_vbl_list,
                             ctx->pre_vbl_list);
  mdd_free (img);
}

static
  void
as_img_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, const PFmla base_a)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  mdd_t* tmp = dst->mdd;
  dst->mdd = mdd_substitute (ctx->ctx, a->mdd,
                             ctx->pre_vbl_list,
                             ctx->img_vbl_list);
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
  PFmla
make1_GluPFmla (PFmlaCtx* fmlactx, bool phase)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  GluPFmla* a = AllocT( GluPFmla, 1 );
  if (phase)
    a->mdd = mdd_one (ctx->ctx);
  else
    a->mdd = mdd_zero (ctx->ctx);
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
vbl_eqlc_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, uint vbl_id, uint x)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  if (dst->mdd)  mdd_free (dst->mdd);
  dst->mdd = mdd_eq_c (ctx->ctx, id_of_pre (vbl_id), x);
}

static
  void
vbl_img_eqlc_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, uint vbl_id, uint x)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  if (dst->mdd)  mdd_free (dst->mdd);
  dst->mdd = mdd_eq_c (ctx->ctx, id_of_img (vbl_id), x);
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
  array_free( ctx->pre_vbl_list );
  array_free( ctx->img_vbl_list );
  if (ctx->ctx)
    mdd_quit (ctx->ctx);
  return ctx;
}

static
  void
add_vbl_GluPFmlaCtx (PFmlaCtx* fmlactx, uint id)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  array_t* doms = array_alloc(uint, 0);
  array_t* names = array_alloc(char*, 0);
  PFmlaVbl* vbl = (PFmlaVbl*) elt_LgTable (&fmlactx->vbls, id);

  array_insert_last(uint, doms, vbl->domsz);
  array_insert_last(uint, doms, vbl->domsz);
  array_insert_last(const char*, names, cstr_of_AlphaTab (&vbl->name));
  array_insert_last(const char*, names, cstr_of_AlphaTab (&vbl->img_name));
  array_insert_last(uint, ctx->pre_vbl_list, id_of_pre (id));
  array_insert_last(uint, ctx->img_vbl_list, id_of_img (id));

  mdd_create_variables(ctx->ctx, doms, names, 0);
  array_free(doms);
  array_free(names);
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
  array_insert_last(uint, ctx->vbl_lists.s[listid], id_of_pre (vblid));
  array_insert_last(uint, ctx->vbl_lists.s[listid], id_of_img (vblid));
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
    vt.pre_fn          =          pre_GluPFmla;
    vt.pre1_fn         =         pre1_GluPFmla;
    vt.img_fn          =          img_GluPFmla;
    vt.img1_fn         =         img1_GluPFmla;
    vt.as_img_fn       =       as_img_GluPFmla;
    vt.tautology_ck_fn = tautology_ck_GluPFmla;
    vt.unsat_ck_fn     =     unsat_ck_GluPFmla;
    vt.equiv_ck_fn     =     equiv_ck_GluPFmla;
    vt.overlap_ck_fn   =   overlap_ck_GluPFmla;
    vt.subseteq_ck_fn  =  subseteq_ck_GluPFmla;
    vt.make_fn         =         make_GluPFmla;
    vt.make1_fn        =        make1_GluPFmla;
    vt.free_fn         =         free_GluPFmla;
    vt.vbl_eqlc_fn     =     vbl_eqlc_GluPFmla;
    vt.vbl_img_eqlc_fn = vbl_img_eqlc_GluPFmla;
    vt.ctx_lose_fn     =      lose_GluPFmlaCtx;
    vt.ctx_add_vbl_fn  =   add_vbl_GluPFmlaCtx;
    vt.ctx_add_vbl_list_fn = add_vbl_list_GluPFmlaCtx;
    vt.ctx_add_to_vbl_list_fn = add_to_vbl_list_GluPFmlaCtx;
  }
  init1_PFmlaCtx (&ctx->fmlactx, &vt);
  ctx->ctx = mdd_init_empty();
  InitTable( ctx->vbl_lists );
  ctx->pre_vbl_list = array_alloc(uint, 0);
  ctx->img_vbl_list = array_alloc(uint, 0);
  return &ctx->fmlactx;
}

