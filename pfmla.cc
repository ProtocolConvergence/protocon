/**
 * \file pfmla.cc
 * This file has functions for the propositional formula data structure.
 */

#include "pfmla.hh"

/**
 * Commit to using the variables added to this context.
 *
 * A context cannot be really "used" before this initialization
 * function is called.
 **/
  void
PFCtx::commitInitialization()
{
  commit_initialization_PFmlaCtx (this->ctx);
}

/**
 * Output all valuations of variables which satisfy a formula.
 *
 * \param of  Output stream.
 * \param a  The formula.
 * \param setIdx  Only print the variables in this set.
 * \param pfx  Prefix to output before every valuation.
 * \param sfx  Suffix to output after every valuation.
 **/
  ostream&
PFCtx::oput(ostream& of, const PF& a, uint setIdx,
            const string& pfx, const string& sfx) const
{
  (void) a;
  (void) setIdx;
  of << pfx << "/*(NOT IMPLEMENTED)*/" << sfx;
#if 0
  mdd_gen* gen;
  array_t* minterm;
  array_t* vars = vVblLists[setIdx];
  foreach_mdd_minterm(a.vMdd, gen, minterm, vars) {
    of << pfx;
    for (uint i = 0; i < (uint) minterm->num; ++i) {
      uint x = array_fetch(uint, minterm, i);
      uint vidx = array_fetch(uint, vars, i);
      const PFVbl& vbl = vVbls[vidx];
      if (i > 0) {
        of << " && ";
      }
      of << vbl.name << "==" << x;
    }
    of << sfx;
    array_free(minterm);
  }
#endif
  return of;
}

