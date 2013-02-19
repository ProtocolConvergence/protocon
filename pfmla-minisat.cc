
#include "pfmla-minisat.hh"

#define __STDC_LIMIT_MACROS
#define __STDC_FORMAT_MACROS
#include <core/Solver.h>

typedef struct MinisatPFmla MinisatPFmla;

namespace MSat = Minisat;
using MSat::Lit;
using MSat::mkLit;

DeclTableT( clause, MSat::vec<MSat::Lit> );

struct MinisatPFmla
{
  PFmlaBase base;
  MSat::Solver* solver;
  TableT(clause) clauses;
  TableT(clause) assumpts;
};

struct MinisatPFmlaCtx
{
  PFmlaCtx fmlactx;
};

static
  const MinisatPFmla*
ccastup_as_MinisatPFmla (const PFmla g)
{
  return CastUp( const MinisatPFmla, base, g );
}

static
  MinisatPFmla*
castup_as_MinisatPFmla (PFmla g)
{
  return CastUp( MinisatPFmla, base, g );
}

static
  MinisatPFmlaCtx*
castup_as_MinisatPFmlaCtx (PFmlaCtx* fmlactx)
{
  return CastUp( MinisatPFmlaCtx, fmlactx, fmlactx );
}

static
  void
init_clause(MSat::vec<MSat::Lit>* a)
{
  new (a) MSat::vec<MSat::Lit>;
}

static
  void
wipe_MinisatPFmla (MinisatPFmla* a)
{
  delete a->solver;
  a->solver = 0;
  for (uint i = 0; i < a->clauses.sz; ++i) {
    a->clauses.s[i].~vec();
  }
  LoseTable( a->clauses );
  InitTable( a->clauses );
  for (uint i = 0; i < a->assumpts.sz; ++i) {
    a->assumpts.s[i].~vec();
  }
  LoseTable( a->assumpts );
  InitTable( a->assumpts );
}

static
  void
op2_MinisatPFmla (PFmlaCtx* ctx, PFmla* base_c, BitOp op,
                  const PFmla base_a, const PFmla base_b)
{
  const MinisatPFmla* a = ccastup_as_MinisatPFmla (base_a);
  const MinisatPFmla* b = ccastup_as_MinisatPFmla (base_b);
  MinisatPFmla* c = castup_as_MinisatPFmla (*base_c);
  (void) ctx;

  if (op == BitOp_IDEN0) {
    if (c != a) {
      wipe_MinisatPFmla (c);
    }
  }
  else if (op == BitOp_IDEN1) {
    op2_MinisatPFmla (ctx, base_c, BitOp_IDEN0, base_b, base_b);
  }
  else if (op == BitOp_OR) {
    Claim2( a->clauses.sz ,==, 1 );
    Claim2( b->clauses.sz ,==, 1 );

    if (c != a && c != b) {
      wipe_MinisatPFmla (c);
    }
    if (c != a) {
      for (uint i = 0; i < (uint)a->clauses.s[0].size(); ++i)  {
        c->clauses.s[0].push(a->clauses.s[0][i]);
      }
    }
    if (c != b) {
      for (uint i = 0; i < (uint)b->clauses.s[0].size(); ++i)  {
        c->clauses.s[0].push(b->clauses.s[0][i]);
      }
    }
  }
  else if (op == BitOp_AND) {
    if (c != a && c != b) {
      wipe_MinisatPFmla (c);
    }
    if (c != a) {
      for (uint i = 0; i < a->clauses.sz; ++i)  {
        GrowTable( c->clauses, 1 );
        init_clause (TopTable( c->clauses ));
        a->clauses.s[i].copyTo(*TopTable( c->clauses ));
      }
    }
    if (c != b) {
      for (uint i = 0; i < b->clauses.sz; ++i)  {
        GrowTable( c->clauses, 1 );
        init_clause (TopTable( c->clauses ));
        b->clauses.s[i].copyTo(*TopTable( c->clauses ));
      }
    }
  }
  else {
    Claim( 0 );
  }

#if 0
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
#endif
}

static
  PFmla
make_MinisatPFmla (PFmlaCtx* ctx)
{
  MinisatPFmla* a = AllocT( MinisatPFmla, 1 );
  (void) ctx;
  a->solver = 0;
  InitTable( a->clauses );
  InitTable( a->assumpts );
  return &a->base;
}

static
  void
free_MinisatPFmla (PFmlaCtx* ctx, PFmla base_a)
{
  MinisatPFmla* a = castup_as_MinisatPFmla (base_a);
  (void) ctx;
  wipe_MinisatPFmla (a);
  free (a);
}

static
  void
vbl_eqlc_MinisatPFmla (PFmlaCtx* fmlactx, PFmla* base_dst, uint vbl_id, uint x)
{
  MinisatPFmla* dst = castup_as_MinisatPFmla (*base_dst);
  (void) fmlactx;

  wipe_MinisatPFmla (dst);

  Grow1Table( dst->clauses );
  init_clause (&dst->clauses.s[0]);

  Lit lit = mkLit(vbl_id, x == 0 ? false : true);
  dst->clauses.s[0].push(lit);
}

static
  void
commit_initialization_MinisatPFmlaCtx (PFmlaCtx* fmlactx)
{
  //MinisatPFmlaCtx* ctx = castup_as_MinisatPFmlaCtx (fmlactx);
  for (uint i = 0; i < fmlactx->vbls.sz; ++i) {
    PFmlaVbl* vbl = vbl_of_PFmlaCtx (fmlactx, i);
    Claim2( vbl->domsz ,==, 2 );
  }
}

static
  void*
lose_MinisatPFmlaCtx (PFmlaCtx* fmlactx)
{
  MinisatPFmlaCtx* ctx = castup_as_MinisatPFmlaCtx (fmlactx);
  return ctx;
}

  PFmlaCtx*
make_MinisatPFmlaCtx ()
{
  static bool vt_initialized = false;
  static PFmlaOpVT vt;
  MinisatPFmlaCtx* ctx = AllocT( MinisatPFmlaCtx, 1 );
  if (!vt_initialized)
  {
    vt_initialized = true;
    memset (&vt, 0, sizeof (vt));
    vt.op2_fn          =          op2_MinisatPFmla;
    //vt.smooth_vbls_fn  =  smooth_vbls_MinisatPFmla;
    //vt.subst_vbls_fn   =   subst_vbls_MinisatPFmla;
    //vt.tautology_ck_fn = tautology_ck_MinisatPFmla;
    //vt.unsat_ck_fn     =     unsat_ck_MinisatPFmla;
    //vt.equiv_ck_fn     =     equiv_ck_MinisatPFmla;
    //vt.overlap_ck_fn   =   overlap_ck_MinisatPFmla;
    //vt.subseteq_ck_fn  =  subseteq_ck_MinisatPFmla;
    vt.make_fn         =         make_MinisatPFmla;
    vt.free_fn         =         free_MinisatPFmla;
    //vt.vbl_eql_fn      =      vbl_eql_MinisatPFmla;
    vt.vbl_eqlc_fn     =     vbl_eqlc_MinisatPFmla;
    vt.ctx_commit_initialization_fn = commit_initialization_MinisatPFmlaCtx;
    vt.ctx_lose_fn = lose_MinisatPFmlaCtx;
    //vt.ctx_add_vbl_list_fn = add_vbl_list_MinisatPFmlaCtx;
    //vt.ctx_add_to_vbl_list_fn = add_to_vbl_list_MinisatPFmlaCtx;
  }
  init1_PFmlaCtx (&ctx->fmlactx, &vt);
  return &ctx->fmlactx;
}

