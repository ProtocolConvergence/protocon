
#include "pfmla.h"
#include "cx/fileb.h"

  void
init1_PFmlaCtx (PFmlaCtx* ctx, const PFmlaOpVT* vt)
{
  ctx->vbls = dflt1_LgTable (sizeof(PFmlaVbl));
  InitAssocia( AlphaTab, PFmlaVbl*, ctx->vbl_map, swapped_AlphaTab );
  InitTable( ctx->vbl_lists );
  ctx->vt = vt;
}

  void
commit_initialization_PFmlaCtx (PFmlaCtx* ctx)
{
  ctx->vt->ctx_commit_initialization_fn (ctx);
}

  void
free_PFmlaCtx (PFmlaCtx* ctx)
{
  void* mem = 0;
  if (ctx->vt->ctx_lose_fn)
    mem = ctx->vt->ctx_lose_fn (ctx);

  for (ujint i = begidx_LgTable (&ctx->vbls);
       i != Max_ujint;
       i = nextidx_LgTable (&ctx->vbls, i))
  {
    PFmlaVbl* x = (PFmlaVbl*) elt_LgTable (&ctx->vbls, i);
    lose_PFmlaVbl (x);
  }
  lose_LgTable (&ctx->vbls);

  lose_Associa (&ctx->vbl_map);

  for (i ; ctx->vbl_lists.sz)
    LoseTable( ctx->vbl_lists.s[i] );
  LoseTable( ctx->vbl_lists );
  if (mem)
    free (mem);
}

static
  void
pre_op2_PFmla (PFmla* c, const PFmla* a, const PFmla* b)
{
  Claim( a );
  if (a->ctx && b && b->ctx)
    Claim2( a->ctx ,==, b->ctx );

  if (c->ctx != a->ctx)
    wipe_PFmla (c);
}

  void
iden_PFmla (PFmla* b, const PFmla* a)
{
  pre_op2_PFmla (b, a, 0);

  if (!a->ctx)
  {
    *b = *a;
  }
  else
  {
    b->ctx = a->ctx;
    a->ctx->vt->op2_fn (a->ctx, &b->mem, BitOp_IDEN0, a->mem, 0);
  }
}

  void
not_PFmla (PFmla* b, const PFmla* a)
{
  pre_op2_PFmla (b, a, 0);

  if (!a->ctx)
  {
    b->ctx = a->ctx;
    phase_fo_PFmla (b, !phase_of_PFmla (a));
  }
  else
  {
    b->ctx = a->ctx;
    a->ctx->vt->op2_fn (a->ctx, &b->mem, BitOp_NOT0, a->mem, 0);
  }
}

  void
and_PFmla (PFmla* c, const PFmla* a, const PFmla* b)
{
  pre_op2_PFmla (c, a, b);
  if (!a->ctx)
  {
    if (phase_of_PFmla (a))
      iden_PFmla (c, b);
    else
      wipe1_PFmla (c, false);
  }
  else if (!b->ctx)
  {
    if (phase_of_PFmla (b))
      iden_PFmla (c, a);
    else
      wipe1_PFmla (c, false);
  }
  else
  {
    c->ctx = a->ctx;
    a->ctx->vt->op2_fn (a->ctx, &c->mem, BitOp_AND, a->mem, b->mem);
  }
}

  void
or_PFmla (PFmla* c, const PFmla* a, const PFmla* b)
{
  pre_op2_PFmla (c, a, b);
  if (!a->ctx)
  {
    if (phase_of_PFmla (a))
      wipe1_PFmla (c, true);
    else
      iden_PFmla (c, b);
  }
  else if (!b->ctx)
  {
    if (phase_of_PFmla (b))
      wipe1_PFmla (c, true);
    else
      iden_PFmla (c, a);
  }
  else
  {
    c->ctx = a->ctx;
    a->ctx->vt->op2_fn (a->ctx, &c->mem, BitOp_OR, a->mem, b->mem);
  }
}

  void
nimp_PFmla (PFmla* c, const PFmla* a, const PFmla* b)
{
  pre_op2_PFmla (c, a, b);

  if (!a->ctx)
  {
    if (phase_of_PFmla (a))
      not_PFmla (c, b);
    else
      wipe1_PFmla (c, false);
  }
  else if (!b->ctx)
  {
    if (phase_of_PFmla (b))
      wipe1_PFmla (c, false);
    else
      iden_PFmla (c, a);
  }
  else
  {
    c->ctx = a->ctx;
    a->ctx->vt->op2_fn (a->ctx, &c->mem, BitOp_NIMP, a->mem, b->mem);
  }
}


  bool
tautology_ck_PFmla (const PFmla* g)
{
  if (!g->ctx)
    return phase_of_PFmla (g);
  return g->ctx->vt->tautology_ck_fn (g->ctx, g->mem);
}

  bool
unsat_ck_PFmla (const PFmla* g)
{
  if (!g->ctx)
    return !phase_of_PFmla (g);

  if (g->ctx->vt->unsat_ck_fn)
    return g->ctx->vt->unsat_ck_fn (g->ctx, g->mem);

  Claim( g->ctx->vt->tautology_ck_fn );
  {
    PFmla c[1];
    bool ret;
    init_PFmla (c);
    g->ctx->vt->op2_fn (g->ctx, &c->mem, BitOp_NOT0, g->mem, 0);
    ret = g->ctx->vt->tautology_ck_fn (g->ctx, &c->mem);
    lose_PFmla (c);
    return ret;
  }
}

  bool
equiv_ck_PFmla (const PFmla* a, const PFmla* b)
{
  if (!a->ctx)
  {
    if (phase_of_PFmla (a))
      return tautology_ck_PFmla (b);
    else
      return unsat_ck_PFmla (b);
  }
  if (!b->ctx)
  {
    if (phase_of_PFmla (b))
      return tautology_ck_PFmla (a);
    else
      return unsat_ck_PFmla (a);
  }
  if (a->ctx->vt->equiv_ck_fn)
    return a->ctx->vt->equiv_ck_fn (a->ctx, a->mem, b->mem);

  Claim( a->ctx->vt->tautology_ck_fn );
  {
    PFmla c[1];
    bool ret;
    init_PFmla (c);
    a->ctx->vt->op2_fn (a->ctx, &c->mem, BitOp_EQL, a->mem, b->mem);
    ret = a->ctx->vt->tautology_ck_fn (a->ctx, &c->mem);
    lose_PFmla (c);
    return ret;
  }
}

  bool
overlap_ck_PFmla (const PFmla* a, const PFmla* b)
{
  if (!a->ctx)
    return phase_of_PFmla (a) && !unsat_ck_PFmla (b);
  if (!b->ctx)
    return phase_of_PFmla (b) && !unsat_ck_PFmla (a);
  if (a->ctx->vt->overlap_ck_fn)
    return a->ctx->vt->overlap_ck_fn (a->ctx, a->mem, b->mem);

  {
    PFmla c[1];
    bool ret;
    init_PFmla (c);
    and_PFmla (c, a, b);
    ret = !unsat_ck_PFmla (c);
    lose_PFmla (c);
    return ret;
  }
}

  bool
subseteq_ck_PFmla (const PFmla* a, const PFmla* b)
{
  if (!a->ctx)
  {
    if (phase_of_PFmla (a))
      return tautology_ck_PFmla (b);
    return true;
  }
  if (!b->ctx)
  {
    if (phase_of_PFmla (b))
      return true;
    return unsat_ck_PFmla (a);
  }
  if (a->ctx->vt->subseteq_ck_fn)
    return a->ctx->vt->subseteq_ck_fn (a->ctx, a->mem, b->mem);

  {
    PFmla c[1];
    bool ret;
    init_PFmla (c);
    or_PFmla (c, a, b);
    ret = equiv_ck_PFmla (c, b);
    lose_PFmla (c);
    return ret;
  }
}

  void
smooth_vbls_PFmla (PFmla* dst, const PFmla* a, uint list_id)
{
  if (!a->ctx)
  {
    iden_PFmla (dst, a);
  }
  else
  {
    if (dst->ctx != a->ctx)
      wipe_PFmla (dst);
    dst->ctx = a->ctx;
    a->ctx->vt->smooth_vbls_fn (a->ctx, &dst->mem, a->mem, list_id);
  }
}

  void
subst_vbls_PFmla (PFmla* dst, const PFmla* a, uint list_id_new, uint list_id_old)
{
  if (!a->ctx)
  {
    iden_PFmla (dst, a);
  }
  else
  {
    if (dst->ctx != a->ctx)
      wipe_PFmla (dst);
    dst->ctx = a->ctx;
    a->ctx->vt->subst_vbls_fn (a->ctx, &dst->mem, a->mem,
                               list_id_new, list_id_old);
  }
}

  void
eql_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, const PFmlaVbl* b)
{
  Claim2( a->ctx ,==, b->ctx );
  if (dst->ctx != a->ctx)
    wipe_PFmla (dst);

  dst->ctx = a->ctx;
  a->ctx->vt->vbl_eql_fn (a->ctx, &dst->mem, a->id, b->id);
}

  void
eqlc_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, uint x)
{
  if (dst->ctx != a->ctx)
    wipe_PFmla (dst);

  dst->ctx = a->ctx;
  a->ctx->vt->vbl_eqlc_fn (a->ctx, &dst->mem, a->id, x);
}


  uint
add_vbl_PFmlaCtx (PFmlaCtx* ctx, const char* name, uint domsz)
{
  bool added = false;
  PFmlaVbl* x;
  uint id;
  Assoc* assoc;

  id = takeidx_LgTable (&ctx->vbls);
  x = elt_LgTable (&ctx->vbls, id);
  x->ctx = ctx;
  x->name = cons1_AlphaTab (name);
  x->id = id;
  x->domsz = domsz;

  assoc = ensure1_Associa (&ctx->vbl_map, &x->name, &added);
  if (!added) {
    DBog1( "There already exists a variable with name: %s", name );
    lose_PFmlaVbl (x);
    giveidx_LgTable (&ctx->vbls, id);
    return 0;
  }
  *(PFmlaVbl**) val_of_Assoc (assoc) = x;
  return id;
}

  uint
add_vbl_list_PFmlaCtx (PFmlaCtx* ctx)
{
  TableT(uint) t;
  InitTable( t );
  PushTable( ctx->vbl_lists, t );
  return ctx->vbl_lists.sz - 1;
}

  void
add_to_vbl_list_PFmlaCtx (PFmlaCtx* ctx, uint listid, uint vblid)
{
  PushTable( ctx->vbl_lists.s[listid], vblid );
}

