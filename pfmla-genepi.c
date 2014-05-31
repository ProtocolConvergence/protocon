
#include "pfmla-genepi.h"
#include <genepi/genepi-util.h>
#include <genepi/genepi.h>
#include <stdio.h>

typedef struct GenepiPFmla GenepiPFmla;
typedef struct GenepiPFmlaVbl GenepiPFmlaVbl;
typedef struct GenepiPFmlaCtx GenepiPFmlaCtx;

struct GenepiPFmla
{
  PFmlaBase base;
  BitTable cols;
  genepi_set* set;
};

struct GenepiPFmlaVbl
{
  PFmlaVbl base;
  AlphaTab img_name;
  AlphaTab aux_name;
  uint pre_id;
  uint img_id;
  uint aux_id;
};

struct GenepiPFmlaCtx
{
  PFmlaCtx fmlactx;
  genepi_solver* ctx;
};

static
  const GenepiPFmla*
ccastup_as_GenepiPFmla (const PFmla g)
{
  return CastUp( const GenepiPFmla, base, g );
}

static
  GenepiPFmla*
castup_as_GenepiPFmla (PFmla g)
{
  return CastUp( GenepiPFmla, base, g );
}

static
  GenepiPFmlaVbl*
vbl_of_GenepiPFmlaCtx (GenepiPFmlaCtx* ctx, uint id)
{
  PFmlaVbl* x = vbl_of_PFmlaCtx (&ctx->fmlactx, id);
  return CastUp( GenepiPFmlaVbl, base, x );
}

static
  GenepiPFmlaCtx*
castup_as_GenepiPFmlaCtx (PFmlaCtx* fmlactx)
{
  return CastUp( GenepiPFmlaCtx, fmlactx, fmlactx );
}

static
  void*
lose_GenepiPFmlaCtx (PFmlaCtx* fmlactx)
{
  GenepiPFmlaCtx* ctx = castup_as_GenepiPFmlaCtx (fmlactx);
  if (ctx->ctx)
    genepi_solver_delete (ctx->ctx);
  return ctx;
}

  void
init_lib_GenepiPFmla ()
{
  genepi_loader_init ();
  genepi_loader_load_default_plugins ();

  {
    int n=0;
    char** names = genepi_loader_get_plugins (&n);
    for (int i = 0; i < n; ++i) {
      fprintf(stderr, "name: %s\n", names[i]);
    }
  }
}

  void
lose_lib_GenepiPFmla ()
{
  genepi_loader_terminate ();
}

  PFmlaCtx*
make_GenepiPFmlaCtx ()
{
  static bool vt_initialized = false;
  static PFmlaVT vt;
  GenepiPFmlaCtx* ctx = AllocT( GenepiPFmlaCtx, 1 );
  if (!vt_initialized)
  {
    vt_initialized = true;
    memset (&vt, 0, sizeof (vt));
    vt.vbl_base_offset = offsetof(GenepiPFmlaVbl, base);
    vt.vbl_size        = sizeof(GenepiPFmlaVbl);
    //vt.op2_fn          =          op2_GenepiPFmla;
    //vt.smooth_vbls_fn  =  smooth_vbls_GenepiPFmla;
    //vt.subst_vbls_fn   =   subst_vbls_GenepiPFmla;
    //vt.pre_fn          =          pre_GenepiPFmla;
    //vt.pre1_fn         =         pre1_GenepiPFmla;
    //vt.img_as_img_fn   =   img_as_img_GenepiPFmla;
    //vt.img_fn          =          img_GenepiPFmla;
    //vt.img1_fn         =         img1_GenepiPFmla;
    //vt.dotjoin_fn      =      dotjoin_GenepiPFmla;
    //vt.inverse_fn      =      inverse_GenepiPFmla;
    //vt.as_img_fn       =       as_img_GenepiPFmla;
    //vt.tautology_ck_fn = tautology_ck_GenepiPFmla;
    //vt.sat_ck_fn       =       sat_ck_GenepiPFmla;
    //vt.equiv_ck_fn     =     equiv_ck_GenepiPFmla;
    //vt.overlap_ck_fn   =   overlap_ck_GenepiPFmla;
    //vt.subseteq_ck_fn  =  subseteq_ck_GenepiPFmla;
    //vt.make_fn         =         make_GenepiPFmla;
    //vt.make1_fn        =        make1_GenepiPFmla;
    //vt.free_fn         =         free_GenepiPFmla;
    //vt.vbl_lose_fn     =      lose_GenepiPFmlaVbl;
    //vt.vbl_eqc_fn      =      vbl_eqc_GenepiPFmla;
    //vt.vbl_img_eqc_fn  =  vbl_img_eqc_GenepiPFmla;
    vt.ctx_lose_fn     =      lose_GenepiPFmlaCtx;
    //vt.ctx_add_vbl_fn  =   add_vbl_GenepiPFmlaCtx;
    //vt.ctx_add_vbl_list_fn = add_vbl_list_GenepiPFmlaCtx;
    //vt.ctx_add_to_vbl_list_fn = add_to_vbl_list_GenepiPFmlaCtx;
  }
  init1_PFmlaCtx (&ctx->fmlactx, &vt);

  {
    genepi_plugin* plugin = genepi_loader_get_plugin ("ppl");
    ctx->ctx = genepi_solver_create(plugin, 0, 0, 0);
  }
  //InitTable( ctx->vbl_lists );
  //InitTable( ctx->pre_vbl_lists );
  //InitTable( ctx->img_vbl_lists );
  //InitTable( ctx->aux_vbl_lists );
  //ctx->pre_vbl_list = array_alloc(uint, 0);
  //ctx->img_vbl_list = array_alloc(uint, 0);
  //ctx->aux_vbl_list = array_alloc(uint, 0);
  return &ctx->fmlactx;
}

