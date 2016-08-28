
#ifndef PFmla_H_
#define PFmla_H_

#include "cx/alphatab.h"
#include "cx/associa.h"
#include "cx/bittable.h"

typedef struct PFmlaBase PFmlaBase;
typedef PFmlaBase* PFmla;
typedef struct XnPFmla XnPFmla;
typedef struct PFmlaVbl PFmlaVbl;
typedef struct PFmlaCtx PFmlaCtx;
typedef struct PFmlaVT PFmlaVT;

struct PFmlaBase
{
  PFmlaCtx* ctx;
};

struct PFmlaVbl
{
  PFmlaCtx* ctx;
  uint domsz;
  uint id;
  AlphaTab name;
  uint list_id;
};

struct PFmlaCtx
{
  LgTable vbls;
  Associa vbl_map;
  TableT( TableT_uint ) vbl_lists;
  const PFmlaVT* vt;
};

struct PFmlaVT
{
  size_t vbl_base_offset;
  size_t vbl_size;

  void (*op2_fn) (PFmlaCtx*, PFmla*, BitOp, const PFmla, const PFmla);

  void (*smooth_vbls_fn) (PFmlaCtx*, PFmla*, const PFmla, uint, Sign);
  void (*subst1_vbls_fn) (PFmlaCtx*, PFmla*, const PFmla, uint, Bool);
  void (*subst_vbls_fn) (PFmlaCtx*, PFmla*, const PFmla, uint, uint);
  void (*pre_fn) (PFmlaCtx*, PFmla*, const PFmla);
  void (*pre1_fn) (PFmlaCtx*, PFmla*, const PFmla, const PFmla);
  void (*pre2_fn) (PFmlaCtx*, PFmla*, const PFmla, const PFmla, uint);
  void (*img_as_img_fn) (PFmlaCtx*, PFmla*, const PFmla);
  void (*img_fn) (PFmlaCtx*, PFmla*, const PFmla);
  void (*img1_fn) (PFmlaCtx*, PFmla*, const PFmla, const PFmla);
  void (*img2_fn) (PFmlaCtx*, PFmla*, const PFmla, const PFmla, uint);
  void (*dotjoin_fn) (PFmlaCtx*, PFmla*, const PFmla, const PFmla);
  void (*inverse_fn) (PFmlaCtx*, PFmla*, const PFmla);
  void (*as_img_fn) (PFmlaCtx*, PFmla*, const PFmla);
  void (*pick_pre_fn) (PFmlaCtx*, PFmla*, const PFmla);
  bool (*tautology_ck_fn) (PFmlaCtx*, const PFmla);
  bool (*sat_ck_fn) (PFmlaCtx*, const PFmla);
  bool (*equiv_ck_fn) (PFmlaCtx*, const PFmla, const PFmla);
  bool (*overlap_ck_fn) (PFmlaCtx*, const PFmla, const PFmla);
  bool (*subseteq_ck_fn) (PFmlaCtx*, const PFmla, const PFmla);

  PFmla (*make_fn) (PFmlaCtx*);
  PFmla (*make1_fn) (PFmlaCtx*, bool);
  void (*free_fn) (PFmlaCtx*, PFmla);

  void (*vbl_lose_fn) (PFmlaVbl*);
  void (*vbl_eq_fn) (PFmlaCtx*, PFmla*, uint, uint);
  void (*vbl_eqc_fn) (PFmlaCtx*, PFmla*, uint, uint);
  void (*vbl_img_eq_fn) (PFmlaCtx*, PFmla*, uint, uint);
  void (*vbl_img_eqc_fn) (PFmlaCtx*, PFmla*, uint, uint);

  void* (*ctx_lose_fn) (PFmlaCtx*);
  void (*ctx_add_vbl_fn) (PFmlaCtx*, uint);
  uint (*ctx_add_vbl_list_fn) (PFmlaCtx*);
  void (*ctx_add_to_vbl_list_fn) (PFmlaCtx*, uint, uint);
};


void
init1_PFmlaCtx (PFmlaCtx* ctx, const PFmlaVT* vt);
void
free_PFmlaCtx (PFmlaCtx* ctx);


void
wipe1_PFmla (PFmla* g, bool phase);

void
iden_PFmla (PFmla* b, const PFmla a);
void
not_PFmla (PFmla* b, const PFmla a);
void
and_PFmla (PFmla* c, const PFmla a, const PFmla b);
void
or_PFmla (PFmla* c, const PFmla a, const PFmla b);
void
nimp_PFmla (PFmla* c, const PFmla a, const PFmla b);
void
xnor_PFmla (PFmla* c, const PFmla a, const PFmla b);
void
xor_PFmla (PFmla* c, const PFmla a, const PFmla b);

bool
tautology_ck_PFmla (const PFmla g);
bool
sat_ck_PFmla (const PFmla g);
bool
equiv_ck_PFmla (const PFmla a, const PFmla b);
bool
overlap_ck_PFmla (const PFmla a, const PFmla b);
bool
subseteq_ck_PFmla (const PFmla a, const PFmla b);
void
smooth_vbl_PFmla (PFmla* dst, const PFmla a, const PFmlaVbl* vbl, Sign pre_or_img);
void
smooth_vbls_PFmla (PFmla* dst, const PFmla a, uint list_id, Sign pre_or_img);
void
subst1_vbls_PFmla (PFmla* dst, const PFmla a, uint list_id, Bool to_img);
void
subst_vbls_PFmla (PFmla* dst, const PFmla a, uint list_id_new, uint list_id_old);
void
pre_PFmla (PFmla* dst, const PFmla a);
void
pre1_PFmla (PFmla* dst, const PFmla a, const PFmla b);
void
pre2_PFmla (PFmla* dst, const PFmla a, const PFmla b, uint list_id);
void
img_as_img_PFmla (PFmla* dst, const PFmla a);
void
img_PFmla (PFmla* dst, const PFmla a);
void
img1_PFmla (PFmla* dst, const PFmla a, const PFmla b);
void
img2_PFmla (PFmla* dst, const PFmla xn, const PFmla pf, uint list_id);
void
dotjoin_PFmla (PFmla* dst, const PFmla a, const PFmla b);
void
inverse_PFmla (PFmla* dst, const PFmla a);
void
as_img_PFmla (PFmla* dst, const PFmla a);
void
pick_pre_PFmla (PFmla* dst, const PFmla a);
void
state_of_PFmla (uint* state, const PFmla a, const uint* indices, uint n);
void
eq_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, const PFmlaVbl* b);
void
eqc_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, uint x);
void
img_eq_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, const PFmlaVbl* b);
void
img_eqc_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, uint x);
void
img_eq_img_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, const PFmlaVbl* b);

uint
add_vbl_PFmlaCtx (PFmlaCtx* ctx, const char* name, uint domsz);
uint
add_vbl_list_PFmlaCtx (PFmlaCtx* ctx);
void
add_to_vbl_list_PFmlaCtx (PFmlaCtx* ctx, uint listid, uint vblid);

#define DEFAULT_PFmla ((PFmla) NULL)
qual_inline
  PFmla
dflt_PFmla ()
{
  return NULL;
}

qual_inline
  PFmla
dflt1_PFmla (bool phase)
{
  PFmla g = default;
  wipe1_PFmla (&g, phase);
  return g;
}

qual_inline
  void
init_PFmla (PFmla* g)
{
  *g = dflt_PFmla ();
}

qual_inline
  void
init1_PFmla (PFmla* g, bool phase)
{
  *g = dflt1_PFmla (phase);
}

qual_inline
  PFmla
cons_PFmla (PFmlaCtx* ctx)
{
  PFmla g = ctx->vt->make_fn (ctx);
  g->ctx = ctx;
  return g;
}

qual_inline
  PFmla
cons1_PFmla (PFmlaCtx* ctx, bool phase)
{
  PFmla g = ctx->vt->make1_fn (ctx, phase);
  g->ctx = ctx;
  return g;
}

qual_inline
  Trit
phase_of_PFmla (const PFmla g)
{
  if (!g)  return Nil;
  if (!g->ctx)  return Yes;
  return May;
}

qual_inline
  void
init2_PFmla (PFmla* g, bool phase, const PFmla a)
{
  if (May == phase_of_PFmla (a)) {
    *g = cons1_PFmla (a->ctx, phase);
  }
  else {
    init1_PFmla (g, phase);
  }
}

qual_inline
  void
lose_PFmla (PFmla* g)
{
  if (phase_of_PFmla (*g) == May)
    (*g)->ctx->vt->free_fn ((*g)->ctx, *g);
}

qual_inline
  void
lose_PFmlaVbl (PFmlaVbl* x)
{
  if (x->ctx->vt->vbl_lose_fn) {
    x->ctx->vt->vbl_lose_fn (x);
  }
  lose_AlphaTab (&x->name);
}

qual_inline
  void
wipe_PFmla (PFmla* g)
{
  lose_PFmla (g);
  *g = 0;
}

qual_inline
  void
ensure_ctx_PFmla (PFmla* a, PFmlaCtx* ctx)
{
  Trit phase_a = phase_of_PFmla (*a);
  if (phase_a == May)
  {
    Claim2( (*a)->ctx, ==, ctx);
  }
  else
  {
    *a = cons1_PFmla (ctx, phase_a == Yes);
  }
}

qual_inline
  void
fill_ctx_PFmla (PFmla* a, PFmla* b)
{
  Trit phase_a = phase_of_PFmla (*a);
  Trit phase_b = phase_of_PFmla (*b);
  if (phase_a == May)
  {
    ensure_ctx_PFmla (b, (*a)->ctx);
  }
  else if (phase_b == May)
  {
    *a = cons1_PFmla ((*b)->ctx, phase_a == Yes);
  }
  else
  {
    Claim( phase_a == May || phase_b == May );
  }
}

qual_inline
  PFmlaVbl*
vbl_of_PFmlaCtx (PFmlaCtx* ctx, uint id)
{
  return CastOff( PFmlaVbl, elt_LgTable (&ctx->vbls, id)
                  ,+, ctx->vt->vbl_base_offset );
}

qual_inline
  PFmlaVbl*
vbl_lookup_PFmlaCtx (PFmlaCtx* ctx, const char* s)
{
  AlphaTab alpha = dflt1_AlphaTab (s);
  Assoc* assoc = lookup_Associa (&ctx->vbl_map, &alpha);
  return *(PFmlaVbl**) val_of_Assoc (&ctx->vbl_map, assoc);
}

#endif

