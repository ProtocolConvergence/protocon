#ifndef SATSYN_ENCODESAT_H_
#define SATSYN_ENCODESAT_H_
#if defined(__cplusplus)
extern "C" {
#endif
#include "synsearch.h"

typedef struct BoolLit BoolLit;
typedef struct CnfDisj CnfDisj;
typedef struct CnfFmla CnfFmla;

DeclTableT( BoolLit, BoolLit );
DeclTableT( CnfDisj, CnfDisj );

/** Boolean literal.
 * This is a variable that appears in a positive form or negated.
 **/
struct BoolLit {
    Bit  val; /**< Positive (1) or negated (0).**/
    uint vbl; /**< Index of the boolean variable.**/
};

/** Disjunction of boolean literals.**/
struct CnfDisj {
    TableT(BoolLit) lits;
};
#define DEFAULT_CnfDisj { DEFAULT_Table }

/** Boolean formula in Conjunctive Normal Form (CNF).
 * An example CNF is:\n
 * (a || !b || c) && (!b || d) && (b || !a) && (a)
 **/
struct CnfFmla {
    uint nvbls;
    TableT(zuint) idcs;  /**< Clause indices.**/
    TableT(uint) vbls;  /**< Clause variables.**/
    BitTable vals;  /**< Clause values, negative (0) or positive (1).**/
};
#define DEFAULT_CnfFmla { 0, DEFAULT_Table, DEFAULT_Table, DEFAULT_BitTable }

BoolLit
dflt2_BoolLit (bool val, uint vbl);
CnfDisj
dflt_CnfDisj ();
void
lose_CnfDisj (CnfDisj* clause);
void
app_CnfDisj (CnfDisj* clause, bool b, uint vbl);

CnfFmla
dflt_CnfFmla ();
void
lose_CnfFmla (CnfFmla* fmla);
void
app_CnfFmla (CnfFmla* fmla, const CnfDisj* clause);
void
clause_of_CnfFmla (CnfDisj* clause, const CnfFmla* fmla, zuint i);

Sign
cmp_XnSz (const XnSz* a, const XnSz* b);
Sign
cmp_XnSz2 (const XnSz2* a, const XnSz2* b);

CnfFmla
encode_sat(FMem_synsearch* tape);

#if defined(__cplusplus)
}
#endif
#endif  /* #ifndef SATSYN_ENCODESAT_H_ */
