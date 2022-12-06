
#include "pfmla.h"
#include <assert.h>

  void
init1_PFmlaCtx (PFmlaCtx* ctx, const PFmlaVT* vt)
{
  const FildeshKV empty_map = DEFAULT_FildeshKV_SINGLE_LIST;
  assert(vt->vbl_base_offset == 0);
  init_FildeshAT(ctx->vbls);
  ctx->vbl_map = empty_map;
  ctx->alloc = open_FildeshAlloc();
  InitTable( ctx->vbl_lists );
  ctx->vt = vt;
}

  void
free_PFmlaCtx (PFmlaCtx* ctx)
{
  void* mem = 0;
  if (ctx->vt->ctx_lose_fn)
    mem = ctx->vt->ctx_lose_fn (ctx);

  for (size_t i = 0; i < count_of_FildeshAT(ctx->vbls); ++i) {
    lose_PFmlaVbl((*ctx->vbls)[i]);
  }
  close_FildeshAT(ctx->vbls);
  close_FildeshKV(&ctx->vbl_map);
  close_FildeshAlloc(ctx->alloc);

  for (uint i = 0; i < ctx->vbl_lists.sz; ++i)
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
sat_ck_PFmla (const PFmla g)
{
  Trit phase = phase_of_PFmla (g);
  if (phase != May)
    return phase == Yes;

  VTCall( g->ctx->vt, return,sat_ck_fn,(g->ctx, g) );

  Claim( g->ctx->vt->tautology_ck_fn );
  {
    PFmla c = DEFAULT_PFmla;
    bool ret;
    g->ctx->vt->op2_fn (g->ctx, &c, BitOp_NOT0, g, g);
    ret = g->ctx->vt->tautology_ck_fn (g->ctx, c);
    lose_PFmla (&c);
    return !ret;
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
      return !sat_ck_PFmla (b);
  }
  if (phase_b != May)
  {
    if (phase_b == Yes)
      return tautology_ck_PFmla (a);
    else
      return !sat_ck_PFmla (a);
  }

  Claim2( a->ctx ,==, b->ctx );
  VTCall( a->ctx->vt, return,equiv_ck_fn,(a->ctx, a, b) );

  Claim( a->ctx->vt->tautology_ck_fn );
  {
    PFmla c = DEFAULT_PFmla;
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
      return sat_ck_PFmla (b);
    return false;
  }
  if (phase_b != May)
  {
    if (phase_b == Yes)
      return sat_ck_PFmla (a);
    return false;
  }

  Claim2( a->ctx ,==, b->ctx );
  if (a->ctx->vt->overlap_ck_fn)
    return a->ctx->vt->overlap_ck_fn (a->ctx, a, b);

  {
    PFmla c = DEFAULT_PFmla;
    bool ret;
    and_PFmla (&c, a, b);
    ret = sat_ck_PFmla (c);
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
    return !sat_ck_PFmla (a);
  }

  Claim2( a->ctx ,==, b->ctx );
  VTCall( a->ctx->vt, return,subseteq_ck_fn,(a->ctx, a, b) );

  {
    PFmla c = DEFAULT_PFmla;
    bool ret;
    or_PFmla (&c, a, b);
    ret = equiv_ck_PFmla (c, b);
    lose_PFmla (&c);
    return ret;
  }
}

  void
smooth_vbl_PFmla (PFmla* dst, const PFmla a, const PFmlaVbl* vbl,
                  Sign pre_or_img)
{
  smooth_vbls_PFmla (dst, a, vbl->list_id, pre_or_img);
}

  void
smooth_vbls_PFmla (PFmla* b, const PFmla a, uint list_id, Sign pre_or_img)
{
  Trit phase = phase_of_PFmla (a);
  if (phase != May)
  {
    wipe1_PFmla (b, phase == Yes);
  }
  else
  {
    pre_op2_PFmla (b, a, a);
    a->ctx->vt->smooth_vbls_fn (a->ctx, b, a, list_id, pre_or_img);
  }
}

  void
subst1_vbls_PFmla (PFmla* dst, const PFmla a, uint list_id, Bool to_img)
{
  Trit phase = phase_of_PFmla (a);
  if (phase != May)
  {
    wipe1_PFmla (dst, phase == Yes);
  }
  else
  {
    pre_op2_PFmla (dst, a, a);
    a->ctx->vt->subst1_vbls_fn (a->ctx, dst, a, list_id, to_img);
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
  else if (phase_a != May)
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
pre2_PFmla (PFmla* dst, const PFmla xn, const PFmla pf, uint list_id)
{
  Trit phase_xn = phase_of_PFmla (xn);
  Trit phase_pf = phase_of_PFmla (pf);
  if (phase_pf != May)
  {
    if (phase_pf == Yes)
      pre_PFmla (dst, xn);
    else
      wipe1_PFmla (dst, false);
  }
  else if (phase_xn != May)
  {
    if (phase_xn == Yes)
      smooth_vbls_PFmla (dst, pf, list_id, -1);
    else
      wipe1_PFmla (dst, false);
  }
  else
  {
    pre_op2_PFmla (dst, xn, pf);
    xn->ctx->vt->pre2_fn (xn->ctx, dst, xn, pf, list_id);
  }
}

  void
img_as_img_PFmla (PFmla* dst, const PFmla a)
{
  Trit phase = phase_of_PFmla (a);
  if (phase != May)
  {
    wipe1_PFmla (dst, phase == Yes);
  }
  else
  {
    pre_op2_PFmla (dst, a, a);
    a->ctx->vt->img_as_img_fn (a->ctx, dst, a);
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
img2_PFmla (PFmla* dst, const PFmla xn, const PFmla pf, uint list_id)
{
  Trit phase_xn = phase_of_PFmla (xn);
  Trit phase_pf = phase_of_PFmla (pf);
  if (phase_pf != May)
  {
    if (phase_pf == Yes)
      img_PFmla (dst, xn);
    else
      wipe1_PFmla (dst, false);
  }
  else if (phase_xn != May)
  {
    if (phase_xn == Yes)
      smooth_vbls_PFmla (dst, pf, list_id, -1);
    else
      wipe1_PFmla (dst, false);
  }
  else
  {
    pre_op2_PFmla (dst, xn, pf);
    xn->ctx->vt->img2_fn (xn->ctx, dst, xn, pf, list_id);
  }
}

  void
dotjoin_PFmla (PFmla* dst, const PFmla a, const PFmla b)
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
  else if (phase_a != May)
  {
    if (phase_a == Yes)
      img_as_img_PFmla (dst, b);
    else
      wipe1_PFmla (dst, false);
  }
  else
  {
    pre_op2_PFmla (dst, a, b);
    a->ctx->vt->dotjoin_fn (a->ctx, dst, a, b);
  }
}

  void
inverse_PFmla (PFmla* dst, const PFmla a)
{
  Trit phase = phase_of_PFmla (a);
  if (phase != May)
  {
    wipe1_PFmla (dst, phase == Yes);
  }
  else
  {
    pre_op1_PFmla (dst, a);
    a->ctx->vt->inverse_fn (a->ctx, dst, a);
  }
}

  void
as_img_PFmla (PFmla* dst, const PFmla a)
{
  Trit phase_a = phase_of_PFmla (a);
  if (phase_a != May)
  {
    wipe1_PFmla (dst, (phase_a == Yes));
  }
  else
  {
    pre_op1_PFmla (dst, a);
    a->ctx->vt->as_img_fn (a->ctx, dst, a);
  }
}

  void
pick_pre_PFmla (PFmla* dst, const PFmla a)
{
  Trit phase_a = phase_of_PFmla (a);
  if (phase_a != May)
  {
    Claim( (phase_a == Nil) && "No context available." );
    wipe1_PFmla (dst, false);
  }
  else if (a->ctx->vt->pick_pre_fn)
  {
    pre_op1_PFmla (dst, a);
    a->ctx->vt->pick_pre_fn (a->ctx, dst, a);
  }
  else
  {
    PFmlaCtx* ctx = a->ctx;
    PFmla eq = DEFAULT_PFmla;
    PFmla conj = dflt1_PFmla (true);
    PFmla tmp_conj = DEFAULT_PFmla;

    for (uint i = 0; i < count_of_FildeshAT(ctx->vbls); ++i) {
      const PFmlaVbl* vbl = vbl_of_PFmlaCtx (ctx, i);
      bool found = false;
      for (uint val = 0; !found && val < vbl->domsz-1; ++val) {
        eqc_PFmlaVbl (&eq, vbl, val);
        and_PFmla (&tmp_conj, conj, eq);
        if (overlap_ck_PFmla (tmp_conj, a))
          found = true;
      }
      if (!found) {
        eqc_PFmlaVbl (&eq, vbl, vbl->domsz-1);
      }
      and_PFmla (&conj, conj, eq);
    }
    iden_PFmla (dst, conj);
    lose_PFmla (&tmp_conj);
    lose_PFmla (&conj);
    lose_PFmla (&eq);
  }
}

  void
state_of_PFmla (uint* state, const PFmla a, const uint* indices, uint n)
{
  Trit phase_a = phase_of_PFmla (a);
  if (phase_a != May)
  {
    Claim( (phase_a == Yes) && "No satisfying state." );
    for (uint i = 0; i < n; ++i)  state[i] = 0;
  }
  else
  {
    PFmlaCtx* ctx = a->ctx;
    PFmla eq = DEFAULT_PFmla;
    PFmla conj = dflt1_PFmla (true);
    PFmla tmp_conj = DEFAULT_PFmla;

    for (uint i = 0; i < n; ++i) {
      const PFmlaVbl* vbl = vbl_of_PFmlaCtx (ctx, indices[i]);
      bool found = false;
      for (uint val = 0; val < vbl->domsz-1; ++val) {
        eqc_PFmlaVbl (&eq, vbl, val);
        and_PFmla (&tmp_conj, conj, eq);
        if (overlap_ck_PFmla (tmp_conj, a)) {
          found = true;
          state[i] = val;
          break;
        }
      }
      if (!found) {
        eqc_PFmlaVbl (&eq, vbl, vbl->domsz-1);
        state[i] = vbl->domsz-1;
      }
      and_PFmla (&conj, conj, eq);
    }
    lose_PFmla (&tmp_conj);
    lose_PFmla (&conj);
    lose_PFmla (&eq);
  }
}

  void
eq_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, const PFmlaVbl* b)
{
  Claim2( a->ctx ,==, b->ctx );
  pre_op_ctx_PFmla (dst, a->ctx);
  if (a->ctx->vt->vbl_eq_fn) {
    a->ctx->vt->vbl_eq_fn (a->ctx, dst, a->id, b->id);
  }
  else {
    const uint n = (a->domsz <= b->domsz) ? a->domsz : b->domsz;
    PFmla tmp_a = DEFAULT_PFmla;
    PFmla tmp_b = DEFAULT_PFmla;

    wipe1_PFmla (dst, false);
    for (uint i = 0; i < n; ++i) {
      eqc_PFmlaVbl (&tmp_a, a, i);
      eqc_PFmlaVbl (&tmp_b, b, i);
      and_PFmla (&tmp_a, tmp_a, tmp_b);
      or_PFmla (dst, *dst, tmp_a);
    }
    lose_PFmla (&tmp_a);
    lose_PFmla (&tmp_b);
  }
}

  void
eqc_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, uint x)
{
  if (x >= a->domsz) {
    wipe1_PFmla (dst, false);
    return;
  }
  pre_op_ctx_PFmla (dst, a->ctx);
  a->ctx->vt->vbl_eqc_fn (a->ctx, dst, a->id, x);
}

  void
img_eq_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, const PFmlaVbl* b)
{
  Claim2( a->ctx ,==, b->ctx );
  pre_op_ctx_PFmla (dst, a->ctx);
  if (a->ctx->vt->vbl_img_eq_fn) {
    a->ctx->vt->vbl_img_eq_fn (a->ctx, dst, a->id, b->id);
  }
  else {
    // Use the RHS domain size rather than the minimum in order to be
    // consistent with img_eqc_PFmla(), which computes equality mod the RHS.
    const uint domsz = b->domsz;
    PFmla tmp_a = DEFAULT_PFmla;
    PFmla tmp_b = DEFAULT_PFmla;

    wipe1_PFmla (dst, false);
    for (uint i = 0; i < domsz; ++i) {
      img_eqc_PFmlaVbl (&tmp_a, a, i);
      eqc_PFmlaVbl (&tmp_b, b, i);
      and_PFmla (&tmp_a, tmp_a, tmp_b);
      or_PFmla (dst, *dst, tmp_a);
    }
    lose_PFmla (&tmp_a);
    lose_PFmla (&tmp_b);
  }
}

  void
img_eqc_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, uint x)
{
  if (x >= a->domsz) {
    x %= a->domsz;
  }
  pre_op_ctx_PFmla (dst, a->ctx);
  a->ctx->vt->vbl_img_eqc_fn (a->ctx, dst, a->id, x);
}

  void
img_eq_img_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, const PFmlaVbl* b)
{
  Claim2( a->ctx ,==, b->ctx );
  pre_op_ctx_PFmla (dst, a->ctx);

  {
    // Use the RHS domain size rather than the minimum in order to be
    // consistent with img_eqc_PFmla(), which computes equality mod the RHS.
    const uint domsz = b->domsz;
    PFmla tmp_a = DEFAULT_PFmla;
    PFmla tmp_b = DEFAULT_PFmla;

    wipe1_PFmla (dst, false);
    for (uint i = 0; i < domsz; ++i) {
      img_eqc_PFmlaVbl (&tmp_a, a, i);
      img_eqc_PFmlaVbl (&tmp_b, b, i);
      and_PFmla (&tmp_a, tmp_a, tmp_b);
      or_PFmla (dst, *dst, tmp_a);
    }
    lose_PFmla (&tmp_a);
    lose_PFmla (&tmp_b);
  }
}

  uint
add_vbl_PFmlaCtx (PFmlaCtx* ctx, const char* name, uint domsz)
{
  PFmlaVbl* x = vbl_lookup_PFmlaCtx(ctx, name);
  uint vbl_id;

  if (x) {
#if 0
    DBog1( "There already exists a variable with name: %s", name );
    return 0;
#else
    //DBog1( "Re-using variable with name: %s", name );
    return x->id;
#endif
  }

  x = (PFmlaVbl*) reserve_FildeshAlloc(
      ctx->alloc, ctx->vt->vbl_size, fildesh_alignof(PFmlaVbl));
  vbl_id = count_of_FildeshAT(ctx->vbls);
  push_FildeshAT(ctx->vbls, x);

  {
    char* key = strdup_FildeshAlloc(ctx->alloc, name);
    const FildeshKV_id_t id = ensure_FildeshKV(
        &ctx->vbl_map, key, strlen(key)+1);
    assign_at_FildeshKV(&ctx->vbl_map, id, &x, sizeof(x));
    x->name = key;
  }

  x->ctx = ctx;
  x->id = vbl_id;
  x->domsz = domsz;
  x->list_id = add_vbl_list_PFmlaCtx (ctx);

  ctx->vt->ctx_add_vbl_fn(ctx, vbl_id);

  add_to_vbl_list_PFmlaCtx (ctx, x->list_id, x->id);

  return vbl_id;
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

