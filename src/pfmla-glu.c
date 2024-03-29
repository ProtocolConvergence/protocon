
#define HAVE_ASSERT_H 1
#include "mdd-glu/mdd.h"

#include "pfmla-glu.h"

typedef struct GluPFmla GluPFmla;
typedef struct GluPFmlaVbl GluPFmlaVbl;
typedef struct GluPFmlaCtx GluPFmlaCtx;
DeclTableT( array_t_memloc, array_t* );

struct GluPFmla
{
  PFmlaBase base;
  mdd_t* mdd;
};

struct GluPFmlaVbl
{
  PFmlaVbl base;
  char* img_name;
  char* aux_name;
  uint pre_id;
  uint img_id;
  uint aux_id;
};

struct GluPFmlaCtx
{
  PFmlaCtx fmlactx;
  mdd_manager* ctx;
  TableT(array_t_memloc) vbl_lists;
  TableT(array_t_memloc) pre_vbl_lists;
  TableT(array_t_memloc) img_vbl_lists;
  TableT(array_t_memloc) aux_vbl_lists;
  array_t* pre_vbl_list;
  array_t* img_vbl_list;
  array_t* aux_vbl_list;
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
  GluPFmlaVbl*
vbl_of_GluPFmlaCtx (GluPFmlaCtx* ctx, uint id)
{
  PFmlaVbl* x = vbl_of_PFmlaCtx (&ctx->fmlactx, id);
  return CastUp( GluPFmlaVbl, base, x );
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
smooth_vbls_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_b, const PFmla base_a,
                      uint set_id, Sign pre_or_img)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  GluPFmla* b = castup_as_GluPFmla (*base_b);
  mdd_t* tmp = b->mdd;
  array_t* list;

  if (pre_or_img < 0)
    list = ctx->pre_vbl_lists.s[set_id];
  else if (pre_or_img > 0)
    list = ctx->img_vbl_lists.s[set_id];
  else
    list = ctx->vbl_lists.s[set_id];

  b->mdd = mdd_smooth (ctx->ctx, a->mdd, list);
  if (tmp)  mdd_free (tmp);
}

static
  void
subst1_vbls_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, const PFmla base_a,
                      uint set_id, Bool to_img)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  array_t* pre_list = ctx->pre_vbl_lists.s[set_id];
  array_t* img_list = ctx->img_vbl_lists.s[set_id];
  mdd_t* tmp = dst->mdd;

  if (to_img)
    dst->mdd = mdd_substitute (ctx->ctx, a->mdd, pre_list, img_list);
  else
    dst->mdd = mdd_substitute (ctx->ctx, a->mdd, img_list, pre_list);
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
  mdd_t* tmp = dst->mdd;
  dst->mdd = mdd_and_smooth (ctx->ctx, a->mdd, subst, ctx->img_vbl_list);
  mdd_free (subst);
  if (tmp)  mdd_free (tmp);
}

static
  void
pre2_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, const PFmla base_xn, const PFmla base_pf, uint set_id)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* xn = ccastup_as_GluPFmla (base_xn);
  const GluPFmla* pf = ccastup_as_GluPFmla (base_pf);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  array_t* pre_list = ctx->pre_vbl_lists.s[set_id];
  array_t* img_list = ctx->img_vbl_lists.s[set_id];
  mdd_t* subst = mdd_substitute (ctx->ctx, pf->mdd, pre_list, img_list);
  mdd_t* tmp = dst->mdd;

  dst->mdd = mdd_and_smooth (ctx->ctx, xn->mdd, subst, img_list);
  mdd_free (subst);
  if (tmp)  mdd_free (tmp);
}

static
  void
img_as_img_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, const PFmla base_a)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  mdd_t* img = mdd_smooth (ctx->ctx, a->mdd, ctx->pre_vbl_list);
  if (dst->mdd)  mdd_free (dst->mdd);
  dst->mdd = img;
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
  mdd_t* img = mdd_and_smooth (ctx->ctx, a->mdd, b->mdd, ctx->pre_vbl_list);
  if (dst->mdd)  mdd_free (dst->mdd);
  dst->mdd = mdd_substitute (ctx->ctx, img,
                             ctx->img_vbl_list,
                             ctx->pre_vbl_list);
  mdd_free (img);
}

static
  void
img2_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, const PFmla base_xn, const PFmla base_pf, uint set_id)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* xn = ccastup_as_GluPFmla (base_xn);
  const GluPFmla* pf = ccastup_as_GluPFmla (base_pf);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  array_t* pre_list = ctx->pre_vbl_lists.s[set_id];
  array_t* img_list = ctx->img_vbl_lists.s[set_id];
  mdd_t* img = mdd_and_smooth (ctx->ctx, xn->mdd, pf->mdd, pre_list);
  if (dst->mdd)  mdd_free (dst->mdd);
  dst->mdd = mdd_substitute (ctx->ctx, img, img_list, pre_list);
  mdd_free (img);
}

static
  void
dotjoin_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, const PFmla base_a, const PFmla base_b)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  const GluPFmla* b = ccastup_as_GluPFmla (base_b);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  mdd_t* tmp_a =
    mdd_substitute (ctx->ctx, a->mdd,
                    ctx->img_vbl_list,
                    ctx->aux_vbl_list);
  mdd_t* tmp_b =
    mdd_substitute (ctx->ctx, b->mdd,
                    ctx->pre_vbl_list,
                    ctx->aux_vbl_list);
  mdd_t* old = dst->mdd;
  dst->mdd =
    mdd_and_smooth (ctx->ctx, tmp_a, tmp_b, ctx->aux_vbl_list);
  mdd_free (tmp_a);
  mdd_free (tmp_b);
  if (old)  mdd_free (old);
}

static
  void
inverse_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, const PFmla base_a)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  mdd_t* tmp0 =
    mdd_substitute (ctx->ctx, a->mdd,
                    ctx->img_vbl_list,
                    ctx->aux_vbl_list);
  mdd_t* tmp1 =
    mdd_substitute (ctx->ctx, tmp0,
                    ctx->pre_vbl_list,
                    ctx->img_vbl_list);
  mdd_free (tmp0);
  if (dst->mdd)  mdd_free (dst->mdd);
  dst->mdd =
    mdd_substitute (ctx->ctx, tmp1,
                    ctx->aux_vbl_list,
                    ctx->pre_vbl_list);
  mdd_free (tmp1);
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
sat_ck_GluPFmla (PFmlaCtx* ctx, const PFmla base_a)
{
  const GluPFmla* a = ccastup_as_GluPFmla (base_a);
  (void) ctx;
  return mdd_is_tautology (a->mdd, 0) ? false : true;
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
lose_GluPFmlaVbl (PFmlaVbl* base)
{
  GluPFmlaVbl* x = CastUp( GluPFmlaVbl, base, base );
  free(x->img_name);
  free(x->aux_name);
}

static
  void
vbl_eqc_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, uint vbl_id, uint x)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmlaVbl* vbl = vbl_of_GluPFmlaCtx (ctx, vbl_id);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  if (dst->mdd)  mdd_free (dst->mdd);
  dst->mdd = mdd_eq_c (ctx->ctx, vbl->pre_id, x);
}

static
  void
vbl_img_eqc_GluPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, uint vbl_id, uint x)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmlaVbl* vbl = vbl_of_GluPFmlaCtx (ctx, vbl_id);
  GluPFmla* dst = castup_as_GluPFmla (*base_dst);
  if (dst->mdd)  mdd_free (dst->mdd);
  dst->mdd = mdd_eq_c (ctx->ctx, vbl->img_id, x);
}

static
  void*
lose_GluPFmlaCtx (PFmlaCtx* fmlactx)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  if (ctx->vbl_lists.sz > 0)
  {
    for (uint i = 0; i < ctx->vbl_lists.sz; ++i) {
      array_free(ctx->vbl_lists.s[i]);
      array_free(ctx->pre_vbl_lists.s[i]);
      array_free(ctx->img_vbl_lists.s[i]);
      array_free(ctx->aux_vbl_lists.s[i]);
    }
    LoseTable( ctx->vbl_lists );
    LoseTable( ctx->pre_vbl_lists );
    LoseTable( ctx->img_vbl_lists );
    LoseTable( ctx->aux_vbl_lists );
  }
  array_free( ctx->pre_vbl_list );
  array_free( ctx->img_vbl_list );
  array_free( ctx->aux_vbl_list );
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
  PFmlaVbl* vbl = vbl_of_PFmlaCtx (fmlactx, id);
  GluPFmlaVbl* x = CastUp( GluPFmlaVbl, base, vbl );
  size_t n;

  n = strlen(vbl->name);
  x->img_name = (char*)malloc(n+2);
  x->aux_name = (char*)malloc(n+3);
  memcpy(x->img_name, vbl->name, n);
  memcpy(x->aux_name, vbl->name, n);
  x->img_name[n] = '\'';
  x->img_name[n+1] = '\0';
  x->aux_name[n] = '\'';
  x->aux_name[n+1] = '\'';
  x->aux_name[n+2] = '\0';
  n = 0;

  x->pre_id = vbl->id * 3 + 2;
  x->img_id = vbl->id * 3 + 1;
  x->aux_id = vbl->id * 3;

  array_insert_last(uint, doms, vbl->domsz);
  array_insert_last(uint, doms, vbl->domsz);
  array_insert_last(uint, doms, vbl->domsz);
  // Notice that the actual variables are added in the order: aux, img, pre.
  array_insert_last(const char*, names, x->aux_name);
  array_insert_last(const char*, names, x->img_name);
  array_insert_last(const char*, names, vbl->name);
  array_insert_last(uint, ctx->aux_vbl_list, x->aux_id);
  array_insert_last(uint, ctx->img_vbl_list, x->img_id);
  array_insert_last(uint, ctx->pre_vbl_list, x->pre_id);

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
  PushTable( ctx->pre_vbl_lists, array_alloc(uint, 0) );
  PushTable( ctx->img_vbl_lists, array_alloc(uint, 0) );
  PushTable( ctx->aux_vbl_lists, array_alloc(uint, 0) );
  return ctx->vbl_lists.sz - 1;
}

static
  void
add_to_vbl_list_GluPFmlaCtx (PFmlaCtx* fmlactx, uint listid, uint vblid)
{
  GluPFmlaCtx* ctx = castup_as_GluPFmlaCtx (fmlactx);
  const GluPFmlaVbl* vbl = vbl_of_GluPFmlaCtx (ctx, vblid);
  array_insert_last(uint, ctx->vbl_lists.s[listid], vbl->aux_id);
  array_insert_last(uint, ctx->vbl_lists.s[listid], vbl->img_id);
  array_insert_last(uint, ctx->vbl_lists.s[listid], vbl->pre_id);
  array_insert_last(uint, ctx->pre_vbl_lists.s[listid], vbl->pre_id);
  array_insert_last(uint, ctx->img_vbl_lists.s[listid], vbl->img_id);
  array_insert_last(uint, ctx->aux_vbl_lists.s[listid], vbl->aux_id);
}

  PFmlaCtx*
make_GluPFmlaCtx ()
{
  static bool vt_initialized = false;
  static PFmlaVT vt;
  GluPFmlaCtx* ctx = AllocT( GluPFmlaCtx, 1 );
  if (!vt_initialized)
  {
    vt_initialized = true;
    memset (&vt, 0, sizeof (vt));
    vt.vbl_base_offset = offsetof(GluPFmlaVbl, base);
    vt.vbl_size        = sizeof(GluPFmlaVbl);
    vt.op2_fn          =          op2_GluPFmla;
    vt.smooth_vbls_fn  =  smooth_vbls_GluPFmla;
    vt.subst1_vbls_fn  =  subst1_vbls_GluPFmla;
    vt.subst_vbls_fn   =   subst_vbls_GluPFmla;
    vt.pre_fn          =          pre_GluPFmla;
    vt.pre1_fn         =         pre1_GluPFmla;
    vt.pre2_fn         =         pre2_GluPFmla;
    vt.img_as_img_fn   =   img_as_img_GluPFmla;
    vt.img_fn          =          img_GluPFmla;
    vt.img1_fn         =         img1_GluPFmla;
    vt.img2_fn         =         img2_GluPFmla;
    vt.dotjoin_fn      =      dotjoin_GluPFmla;
    vt.inverse_fn      =      inverse_GluPFmla;
    vt.as_img_fn       =       as_img_GluPFmla;
    vt.tautology_ck_fn = tautology_ck_GluPFmla;
    vt.sat_ck_fn       =       sat_ck_GluPFmla;
    vt.equiv_ck_fn     =     equiv_ck_GluPFmla;
    vt.overlap_ck_fn   =   overlap_ck_GluPFmla;
    vt.subseteq_ck_fn  =  subseteq_ck_GluPFmla;
    vt.make_fn         =         make_GluPFmla;
    vt.make1_fn        =        make1_GluPFmla;
    vt.free_fn         =         free_GluPFmla;
    vt.vbl_lose_fn     =      lose_GluPFmlaVbl;
    vt.vbl_eqc_fn      =      vbl_eqc_GluPFmla;
    vt.vbl_img_eqc_fn  =  vbl_img_eqc_GluPFmla;
    vt.ctx_lose_fn     =      lose_GluPFmlaCtx;
    vt.ctx_add_vbl_fn  =   add_vbl_GluPFmlaCtx;
    vt.ctx_add_vbl_list_fn = add_vbl_list_GluPFmlaCtx;
    vt.ctx_add_to_vbl_list_fn = add_to_vbl_list_GluPFmlaCtx;
  }
  init1_PFmlaCtx (&ctx->fmlactx, &vt);
  ctx->ctx = mdd_init_empty();
  InitTable( ctx->vbl_lists );
  InitTable( ctx->pre_vbl_lists );
  InitTable( ctx->img_vbl_lists );
  InitTable( ctx->aux_vbl_lists );
  ctx->pre_vbl_list = array_alloc(uint, 0);
  ctx->img_vbl_list = array_alloc(uint, 0);
  ctx->aux_vbl_list = array_alloc(uint, 0);
  return &ctx->fmlactx;
}

