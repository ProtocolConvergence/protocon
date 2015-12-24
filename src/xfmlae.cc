
#include "xfmlae.hh"

/**
 * Compute the transitive closure starting from some initial states.
 *
 * Transitive closure is pretty slow. Avoid it.
 */
  X::Fmla
X::Fmlae::transitive_closure(const P::Fmla* initial) const
{
  X::Fmla reach( false );
  X::Fmla next( false );

  Table<X::Fmla> xns = ctx->act_unchanged_xfmlas;
  for (bool first = true; first || !reach.equiv_ck(next); first = false)
  {
    reach = next;

    for (uint i = 0; i < this->sz(); ++i)
    {
      if (first) {
        xns[i] &= (*this)[i];
        if (initial)
          next |= xns[i] & *initial;
        else
          next |= xns[i];
      }

      next |= next.dotjoin(xns[i]);
    }
  }
  return reach;
}

/**
 * This uses a variant of the Emerson-Lei algorithm.
 * It simply computes a fixpoint of the transition relation by
 * iteratively computing the image until it does not change.
 */
  bool
X::Fmlae::cycle_ck(P::Fmla* scc, uint* ret_nlayers,
                   const P::Fmla* invariant, const P::Fmla* assumed) const
{
#if 0
  (void) ret_nlayers;
  (void) invariant;
  X::Fmla trans = this->transitive_closure(assumed);
  //X::Fmla trans = ::transitive_closure(this->xfmla() & *assumed);
  P::Fmla span0 = (trans & ctx->identity_xn).pre();
  if (scc) {
    *scc = span0;
  }
  return span0.sat_ck();
#else
  P::Fmla span0( this->pre() & this->img() );
  span0.ensure_ctx(*this->ctx->ctx);

  if (assumed)
    span0 &= *assumed;

  uint nlayers = 1;

  while (true) {
    const P::Fmla& span1 = this->pre(span0);

    if (span0.subseteq_ck(span1))  break;
    if (ret_nlayers) {
      if (invariant) {
        if (!span0.subseteq_ck(*invariant)) {
          nlayers += 1;
        }
      }
      else {
        nlayers += 1;
      }
      if (*ret_nlayers > 0 && nlayers > *ret_nlayers) {
        *ret_nlayers = nlayers;
        return false;
      }
    }
    span0 &= span1;
  }

  while (true) {
    const P::Fmla& span1 = span0 & this->img(span0);
    if (span0.equiv_ck(span1))  break;
    span0 = span1;
  }

  if (scc)
    *scc = span0;
  if (ret_nlayers)
    *ret_nlayers = nlayers;

  return span0.sat_ck();
#endif
}

bool
  X::Fmlae::probabilistic_livelock_ck
(P::Fmla* scc,
 const P::Fmla& assumed) const
{
  return this->probabilistic_livelock_ck(scc, assumed, X::Fmla(false));
}

bool
  X::Fmlae::probabilistic_livelock_ck
(P::Fmla* scc,
 const P::Fmla& assumed,
 const X::Fmla& progress,
 const X::Fmla* global_xn) const
{
  const X::Fmla xn = (global_xn ? *global_xn : this->xfmla());

  P::Fmla span0( assumed );
  P::Fmla span1( xn.pre() );

  span0.ensure_ctx(*this->ctx->ctx);

  do {
    span0 &= span1;
    span1 = false;

    // For each process...
    for (uint i = 0; i < this->sz(); ++i) {
      const X::Fmla& pc_progress_xn =
        (ctx->act_unchanged_xfmlas[i] & progress);

      // This process resolves livelock states
      // where it is enabled to make a progress transition
      // or simply leave the current span.
      P::Fmla resolved
        = ((*this)[i] & pc_progress_xn).pre()
        | this->pre(i, ~span0)
        ;

      // Accumulate states which enable this process
      // but will not be resolved by this process.
      span1 |= this->pre(i) - resolved;
    }
  } while (!span0.subseteq_ck(span1));

  if (scc) {
    span1 = xn.img();
    do {
      span0 &= span1;
      span1 = xn.img(span0);
    } while (!span0.subseteq_ck(span1));

    *scc = span0;
  }
  return span0.sat_ck();
}


