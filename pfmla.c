
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
phase_fo_PFmla (PFmla* g, bool phase)
{
  static PFmlaBase base = { 0 };
  if (phase)  *g = &base;
  else        *g = 0;
}

  void
wipe1_PFmla (PFmla* g, bool phase)
{
  lose_PFmla (g);
  phase_fo_PFmla (g, phase);
}

static
  void
pre_op2_PFmla (PFmla* c, const PFmla a, const PFmla b)
{
  Claim2( a->ctx ,==, b->ctx );
  if (*c && (*c)->ctx != a->ctx)
    wipe_PFmla (c);
  if (phase_of_PFmla (*c) != May)
    *c = cons_PFmla (a->ctx);
}

static
  void
pre_op1_PFmla (PFmla* b, const PFmla a)
{
  pre_op2_PFmla (b, a, a);
}

static
  void
pre_op_ctx_PFmla (PFmla* dst, PFmlaCtx* ctx)
{
  PFmlaBase base;
  base.ctx = ctx;
  pre_op1_PFmla (dst, &base);
}

  void
iden_PFmla (PFmla* b, const PFmla a)
{
  Trit phase = phase_of_PFmla (a);
  if (phase != May)
  {
    wipe1_PFmla (b, phase == Yes);
  }
  else
  {
    pre_op2_PFmla (b, a, a);
    a->ctx->vt->op2_fn (a->ctx, b, BitOp_IDEN0, a, a);
  }
}

  void
not_PFmla (PFmla* b, const PFmla a)
{
  Trit phase = phase_of_PFmla (a);
  if (phase != May)
  {
    wipe1_PFmla (b, phase != Yes);
  }
  else
  {
    pre_op2_PFmla (b, a, a);
    a->ctx->vt->op2_fn (a->ctx, b, BitOp_NOT0, a, a);
  }
}

  void
and_PFmla (PFmla* c, const PFmla a, const PFmla b)
{
  Trit phase_a = phase_of_PFmla (a);
  Trit phase_b = phase_of_PFmla (b);

  if (phase_a != May)
  {
    if (phase_a == Yes)
      iden_PFmla (c, b);
    else
      wipe1_PFmla (c, false);
  }
  else if (phase_b != May)
  {
    if (phase_b == Yes)
      iden_PFmla (c, a);
    else
      wipe1_PFmla (c, false);
  }
  else
  {
    pre_op2_PFmla (c, a, b);
    a->ctx->vt->op2_fn (a->ctx, c, BitOp_AND, a, b);
  }
}

  void
or_PFmla (PFmla* c, const PFmla a, const PFmla b)
{
  Trit phase_a = phase_of_PFmla (a);
  Trit phase_b = phase_of_PFmla (b);

  if (phase_a != May)
  {
    if (phase_a == Yes)
      wipe1_PFmla (c, true);
    else
      iden_PFmla (c, b);
  }
  else if (phase_b != May)
  {
    if (phase_b == Yes)
      wipe1_PFmla (c, true);
    else
      iden_PFmla (c, a);
  }
  else
  {
    pre_op2_PFmla (c, a, b);
    a->ctx->vt->op2_fn (a->ctx, c, BitOp_OR, a, b);
  }
}

  void
nimp_PFmla (PFmla* c, const PFmla a, const PFmla b)
{
  Trit phase_a = phase_of_PFmla (a);
  Trit phase_b = phase_of_PFmla (b);

  if (phase_a != May)
  {
    if (phase_a == Yes)
      not_PFmla (c, b);
    else
      wipe1_PFmla (c, false);
  }
  else if (phase_b != May)
  {
    if (phase_b == Yes)
      wipe1_PFmla (c, false);
    else
      iden_PFmla (c, a);
  }
  else
  {
    pre_op2_PFmla (c, a, b);
    a->ctx->vt->op2_fn (a->ctx, c, BitOp_NIMP, a, b);
  }
}

  void
xnor_PFmla (PFmla* c, const PFmla a, const PFmla b)
{
  Trit phase_a = phase_of_PFmla (a);
  Trit phase_b = phase_of_PFmla (b);

  if (phase_a != May)
  {
    if (phase_a == Yes)
      iden_PFmla (c, b);
    else
      not_PFmla (c, b);
  }
  else if (phase_b != May)
  {
    if (phase_b == Yes)
      iden_PFmla (c, a);
    else
      not_PFmla (c, a);
  }
  else
  {
    pre_op2_PFmla (c, a, b);
    a->ctx->vt->op2_fn (a->ctx, c, BitOp_XNOR, a, b);
  }
}

  void
xor_PFmla (PFmla* c, const PFmla a, const PFmla b)
{
  Trit phase_a = phase_of_PFmla (a);
  Trit phase_b = phase_of_PFmla (b);

  if (phase_a != May)
  {
    if (phase_a == Yes)
      not_PFmla (c, b);
    else
      iden_PFmla (c, b);
  }
  else if (phase_b != May)
  {
    if (phase_b == Yes)
      not_PFmla (c, a);
    else
      iden_PFmla (c, a);
  }
  else
  {
    pre_op2_PFmla (c, a, b);
    a->ctx->vt->op2_fn (a->ctx, c, BitOp_XOR, a, b);
  }
}

  bool
tautology_ck_PFmla (const PFmla g)
{
  Trit phase = phase_of_PFmla (g);
  if (phase != May)
    return phase == Yes;
  return g->ctx->vt->tautology_ck_fn (g->ctx, g);
}

  bool
unsat_ck_PFmla (const PFmla g)
{
  Trit phase = phase_of_PFmla (g);
  if (phase != May)
    return phase == Nil;

  if (g->ctx->vt->unsat_ck_fn)
    return g->ctx->vt->unsat_ck_fn (g->ctx, g);

  Claim( g->ctx->vt->tautology_ck_fn );
  {
    PFmla c = dflt_PFmla ();
    bool ret;
    g->ctx->vt->op2_fn (g->ctx, &c, BitOp_NOT0, g, g);
    ret = g->ctx->vt->tautology_ck_fn (g->ctx, c);
    lose_PFmla (&c);
    return ret;
  }
}

  bool
equiv_ck_PFmla (const PFmla a, const PFmla b)
{
  Trit phase_a = phase_of_PFmla (a);
  Trit phase_b = phase_of_PFmla (b);

  if (phase_a != May)
  {
    if (phase_a == Yes)
      return tautology_ck_PFmla (b);
    else
      return unsat_ck_PFmla (b);
  }
  if (phase_b != May)
  {
    if (phase_b == Yes)
      return tautology_ck_PFmla (a);
    else
      return unsat_ck_PFmla (a);
  }

  Claim2( a->ctx ,==, b->ctx );
  if (a->ctx->vt->equiv_ck_fn)
    return a->ctx->vt->equiv_ck_fn (a->ctx, a, b);

  Claim( a->ctx->vt->tautology_ck_fn );
  {
    PFmla c = dflt_PFmla ();
    bool ret;
    a->ctx->vt->op2_fn (a->ctx, &c, BitOp_XNOR, a, b);
    ret = a->ctx->vt->tautology_ck_fn (a->ctx, c);
    lose_PFmla (&c);
    return ret;
  }
}

  bool
overlap_ck_PFmla (const PFmla a, const PFmla b)
{
  Trit phase_a = phase_of_PFmla (a);
  Trit phase_b = phase_of_PFmla (b);

  if (phase_a != May)
  {
    if (phase_a == Yes)
      return !unsat_ck_PFmla (b);
    return false;
  }
  if (phase_b != May)
  {
    if (phase_b == Yes)
      return !unsat_ck_PFmla (a);
    return false;
  }

  Claim2( a->ctx ,==, b->ctx );
  if (a->ctx->vt->overlap_ck_fn)
    return a->ctx->vt->overlap_ck_fn (a->ctx, a, b);

  {
    PFmla c = dflt_PFmla ();
    bool ret;
    and_PFmla (&c, a, b);
    ret = !unsat_ck_PFmla (c);
    lose_PFmla (&c);
    return ret;
  }
}

  bool
subseteq_ck_PFmla (const PFmla a, const PFmla b)
{
  Trit phase_a = phase_of_PFmla (a);
  Trit phase_b = phase_of_PFmla (b);

  if (phase_a != May)
  {
    if (phase_a == Yes)
      return tautology_ck_PFmla (b);
    return true;
  }
  if (phase_b != May)
  {
    if (phase_b == Yes)
      return true;
    return unsat_ck_PFmla (a);
  }

  Claim2( a->ctx ,==, b->ctx );
  if (a->ctx->vt->subseteq_ck_fn)
    return a->ctx->vt->subseteq_ck_fn (a->ctx, a, b);

  {
    PFmla c = dflt_PFmla ();
    bool ret;
    or_PFmla (&c, a, b);
    ret = equiv_ck_PFmla (c, b);
    lose_PFmla (&c);
    return ret;
  }
}

  void
smooth_vbls_PFmla (PFmla* b, const PFmla a, uint list_id)
{
  Trit phase = phase_of_PFmla (a);
  if (phase != May)
  {
    wipe1_PFmla (b, phase == Yes);
  }
  else
  {
    pre_op2_PFmla (b, a, a);
    a->ctx->vt->smooth_vbls_fn (a->ctx, b, a, list_id);
  }
}

  void
subst_vbls_PFmla (PFmla* b, const PFmla a, uint list_id_new, uint list_id_old)
{
  Trit phase = phase_of_PFmla (a);
  if (phase != May)
  {
    wipe1_PFmla (b, phase == Yes);
  }
  else
  {
    pre_op2_PFmla (b, a, a);
    a->ctx->vt->subst_vbls_fn (a->ctx, b, a, list_id_new, list_id_old);
  }
}

  void
pre_PFmla (PFmla* dst, const PFmla a)
{
  Trit phase = phase_of_PFmla (a);
  if (phase != May)
  {
    wipe1_PFmla (dst, phase == Yes);
  }
  else
  {
    pre_op2_PFmla (dst, a, a);
    a->ctx->vt->pre_fn (a->ctx, dst, a);
  }
}

  void
pre1_PFmla (PFmla* dst, const PFmla a, const PFmla b)
{
  Trit phase_a = phase_of_PFmla (a);
  Trit phase_b = phase_of_PFmla (b);
  if (phase_b != May)
  {
    if (phase_b == Yes)
      pre_PFmla (dst, a);
    else
      wipe1_PFmla (dst, false);
  }
  if (phase_a != May)
  {
    wipe1_PFmla (dst, phase_a == Yes);
  }
  else
  {
    pre_op2_PFmla (dst, a, b);
    a->ctx->vt->pre1_fn (a->ctx, dst, a, b);
  }
}

  void
img_PFmla (PFmla* dst, const PFmla a)
{
  Trit phase = phase_of_PFmla (a);
  if (phase != May)
  {
    wipe1_PFmla (dst, phase == Yes);
  }
  else
  {
    pre_op2_PFmla (dst, a, a);
    a->ctx->vt->img_fn (a->ctx, dst, a);
  }
}

  void
img1_PFmla (PFmla* dst, const PFmla a, const PFmla b)
{
  Trit phase_a = phase_of_PFmla (a);
  Trit phase_b = phase_of_PFmla (b);
  if (phase_b != May)
  {
    if (phase_b == Yes)
      img_PFmla (dst, a);
    else
      wipe1_PFmla (dst, false);
  }
  else if (phase_a != May)
  {
    wipe1_PFmla (dst, phase_a == Yes);
  }
  else
  {
    pre_op2_PFmla (dst, a, b);
    a->ctx->vt->img1_fn (a->ctx, dst, a, b);
  }
}

  void
eql_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, const PFmlaVbl* b)
{
  Claim2( a->ctx ,==, b->ctx );
  pre_op_ctx_PFmla (dst, a->ctx);
  if (a->ctx->vt->vbl_eql_fn) {
    a->ctx->vt->vbl_eql_fn (a->ctx, dst, a->id, b->id);
  }
  else {
    const uint n = (a->domsz <= b->domsz) ? a->domsz : b->domsz;
    PFmla tmp_a = dflt_PFmla ();
    PFmla tmp_b = dflt_PFmla ();

    wipe1_PFmla (dst, false);
    for (uint i = 0; i < n; ++i) {
      eqlc_PFmlaVbl (&tmp_a, a, i);
      eqlc_PFmlaVbl (&tmp_b, b, i);
      and_PFmla (&tmp_a, tmp_a, tmp_b);
      or_PFmla (dst, *dst, tmp_a);
    }
    lose_PFmla (&tmp_a);
    lose_PFmla (&tmp_b);
  }
}

  void
eqlc_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, uint x)
{
  if (x >= a->domsz) {
    wipe1_PFmla (dst, false);
    return;
  }
  pre_op_ctx_PFmla (dst, a->ctx);
  a->ctx->vt->vbl_eqlc_fn (a->ctx, dst, a->id, x);
}

  void
img_eql_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, const PFmlaVbl* b)
{
  Claim2( a->ctx ,==, b->ctx );
  pre_op_ctx_PFmla (dst, a->ctx);
  if (a->ctx->vt->vbl_img_eql_fn) {
    a->ctx->vt->vbl_img_eql_fn (a->ctx, dst, a->id, b->id);
  }
  else {
    // n is the domain size of RHS since img_eqlc_PFmla() does mod.
    const uint n = b->domsz;
    PFmla tmp_a = dflt_PFmla ();
    PFmla tmp_b = dflt_PFmla ();

    wipe1_PFmla (dst, false);
    for (uint i = 0; i < n; ++i) {
      img_eqlc_PFmlaVbl (&tmp_a, a, i);
      eqlc_PFmlaVbl (&tmp_b, b, i);
      and_PFmla (&tmp_a, tmp_a, tmp_b);
      or_PFmla (dst, *dst, tmp_a);
    }
    lose_PFmla (&tmp_a);
    lose_PFmla (&tmp_b);
  }
}

  void
img_eqlc_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, uint x)
{
  if (x >= a->domsz) {
    x %= a->domsz;
  }
  pre_op_ctx_PFmla (dst, a->ctx);
  a->ctx->vt->vbl_img_eqlc_fn (a->ctx, dst, a->id, x);
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
  x->img_name = cons1_AlphaTab (name);
  cat_cstr_AlphaTab (&x->img_name, "'");
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

  ctx->vt->ctx_add_vbl_fn (ctx, id);

  return id;
}

  uint
add_vbl_list_PFmlaCtx (PFmlaCtx* ctx)
{
  uint listid;
  TableT(uint) t;
  InitTable( t );
  listid = ctx->vbl_lists.sz;
  PushTable( ctx->vbl_lists, t );
  if (ctx->vt->ctx_add_vbl_list_fn)
  {
    uint id = ctx->vt->ctx_add_vbl_list_fn (ctx);
    Claim2( listid ,==, id );
  }
  return listid;
}

  void
add_to_vbl_list_PFmlaCtx (PFmlaCtx* ctx, uint listid, uint vblid)
{
  PushTable( ctx->vbl_lists.s[listid], vblid );
  if (ctx->vt->ctx_add_to_vbl_list_fn)
    ctx->vt->ctx_add_to_vbl_list_fn (ctx, listid, vblid);
}

