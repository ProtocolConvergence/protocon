
#ifndef PFmla_H_
#define PFmla_H_

#include "cx/alphatab.h"
#include "cx/associa.h"
#include "cx/bittable.h"

typedef struct PFmla PFmla;
typedef struct PFmlaVbl PFmlaVbl;
typedef struct PFmlaCtx PFmlaCtx;

typedef struct PFmlaOpVT PFmlaOpVT;
struct PFmlaOpVT
{
  void (*op2_fn) (PFmlaCtx*, void**, BitOp, const void*, const void*);

  void (*exist_set_fn) (PFmlaCtx*, void**, const void*, uint);
  void (*subst_set_fn) (PFmlaCtx*, void**, const void*, uint, uint);
  bool (*tautology_ck_fn) (PFmlaCtx*, const void*);
  bool (*unsat_ck_fn) (PFmlaCtx*, const void*);
  bool (*equiv_ck_fn) (PFmlaCtx*, const void*, const void*);
  bool (*overlap_ck_fn) (PFmlaCtx*, const void*, const void*);
  bool (*subseteq_ck_fn) (PFmlaCtx*, const void*, const void*);
  void (*lose_fn) (PFmlaCtx*, void*);

  void (*vbl_eql_fn) (PFmlaCtx*, void**, uint, uint);
  void (*vbl_eqlc_fn) (PFmlaCtx*, void**, uint, uint);

  void (*ctx_commit_initialization_fn) (PFmlaCtx*);
  void (*ctx_lose_fn) (PFmlaCtx*);
};

struct PFmla
{
  PFmlaCtx* ctx;
  bool phase;
  void* mem;
};

struct PFmlaVbl
{
  PFmlaCtx* ctx;
  uint id;
  AlphaTab name;
  uint domsz;
};

struct PFmlaCtx
{
  LgTable vbls;
  Associa vbl_map;
  TableT( TableT_uint ) vbl_lists;
  const PFmlaOpVT* vt;
};


void
init1_PFmlaCtx (PFmlaCtx* ctx, const PFmlaOpVT* vt);
void
iden_PFmla (PFmla* b, const PFmla* a);
void
not_PFmla (PFmla* b, const PFmla* a);
void
and_PFmla (PFmla* c, const PFmla* a, const PFmla* b);
void
or_PFmla (PFmla* c, const PFmla* a, const PFmla* b);
void
nimp_PFmla (PFmla* c, const PFmla* a, const PFmla* b);

bool
tautology_ck_PFmla (const PFmla* g);
bool
unsat_ck_PFmla (const PFmla* g);
bool
equiv_ck_PFmla (const PFmla* a, const PFmla* b);
bool
overlap_ck_PFmla (const PFmla* a, const PFmla* b);
bool
subseteq_ck_PFmla (const PFmla* a, const PFmla* b);
void
exist_set_PFmla (PFmla* dst, const PFmla* a, uint set_id);
void
subst_set_PFmla (PFmla* dst, const PFmla* a, uint set_id_new, uint set_id_old);
void
eql_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, const PFmlaVbl* b);
void
eqlc_PFmlaVbl (PFmla* dst, const PFmlaVbl* a, uint x);

qual_inline
  void
init_PFmla (PFmla* g)
{
  g->ctx = 0;
}

qual_inline
  void
lose_PFmla (PFmla* g)
{
  if (!g->ctx)  return;
  g->ctx->vt->lose_fn (g->ctx, g->mem);
}

qual_inline
  void
phase_fo_PFmla (PFmla* g, bool phase)
{
  static void* const MemYes = ((void*)Max_ujint);
  static void* const MemNil = ((void*)0);
  g->mem = (phase ? MemYes : MemNil);
}

qual_inline
  bool
phase_of_PFmla (const PFmla* g)
{
  return !!g->mem;
}

qual_inline
  void
wipe_PFmla (PFmla* g)
{
  lose_PFmla (g);
  g->ctx = 0;
  g->mem = 0;
}

qual_inline
  void
wipe1_PFmla (PFmla* g, bool phase)
{
  lose_PFmla (g);
  g->ctx = 0;
  phase_fo_PFmla (g, phase);
}

qual_inline
  PFmlaVbl*
vbl_of_PFmlaCtx (PFmlaCtx* ctx, uint id)
{
  return (PFmlaVbl*) elt_LgTable (&ctx->vbls, id);
}


#endif

