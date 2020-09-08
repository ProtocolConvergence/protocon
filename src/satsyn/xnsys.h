
#ifndef XnSys_H_
#define XnSys_H_

#include "cx/bittable.h"
#include "cx/fileb.h"

#define NMaxXnPcVbls 10

//typedef luint XnSz;
typedef uint XnSz;
typedef byte XnDomSz;
typedef struct XnSz2 XnSz2;

typedef struct XnVbl XnVbl;
typedef struct XnEVbl XnEVbl;
typedef struct XnPc XnPc;
typedef struct XnRule XnRule;
typedef struct XnVblSymm XnVblSymm;
typedef struct XnPcSymm XnPcSymm;
typedef struct XnSys XnSys;

DeclTableT( XnSz, XnSz );
DeclTableT( XnDomSz, XnDomSz );
DeclTableT( Xns, TableT(XnSz) );
DeclTableT( XnSz2, XnSz2 );

DeclTableT( XnVbl, XnVbl );
DeclTableT( XnEVbl, XnEVbl );
DeclTableT( XnPc, XnPc );
DeclTableT( XnRule, XnRule );
DeclTableT( XnVblSymm, XnVblSymm );
DeclTableT( XnPcSymm, XnPcSymm );

/** Holds two XnSz values.**/
struct XnSz2 { XnSz i; XnSz j; };


/** Variable name.**/
struct XnVblSymm
{
    AlphaTab name;
    XnDomSz domsz;
    XnSz stepsz0; /** Rule enumeration step size.**/
    XnSz stepsz1; /** Equal to zero if read-only.**/
};

/** Symmetric process template.**/
struct XnPcSymm
{
    AlphaTab name;
    TableT(XnVblSymm) ovbls;
    TableT(XnVblSymm) xvbls;
    XnSz nstates;
    XnSz nactxns;

    BitTable allowed_acts;
    BitTable defined_acts;

    /** Processes that share this symmetry.**/
    TableT(XnPc) instances;
};


/** Variable in a transition system.**/
struct XnVbl
{
    AlphaTab name;
    XnDomSz domsz; /**< Maximum value in the domain.**/
    TableT(uint) pcs; /**< List of processes that use this variable.**/
    XnSz nwpcs;  /**< Number of processes with write (and read) permission.**/
    XnSz stepsz; /**< Step size global state space.**/
};

/** Evaluation of an XnVbl.**/
struct XnEVbl
{
    XnDomSz val; /**< Evaluation.**/
    const XnVbl* vbl;
};

/** Process in a transition system.**/
struct XnPc
{
    /** Variables this process uses.
     * Variables that this process can write all appear at the beginning.
     **/
    TableT(uint) vbls;
    /** Number of variables for which this
     * process has write and read permissions.
     **/
    XnSz nwvbls;

    XnSz nstates; /**< Same as /legit.sz/.**/

    XnSz rule_step;
    TableT(XnSz) rule_stepsz_p;
    TableT(XnSz) rule_stepsz_q;

    uint symmetry_idx;
};


/** Transition rule (aka "action" or "transition group").**/
struct XnRule
{
    uint pc; /**< Process to which this rule belongs.**/
    FixTableT(XnDomSz, NMaxXnPcVbls) p; /**< Local state of the process to enable this action.**/
    FixTableT(XnDomSz, NMaxXnPcVbls) q; /**< New values of writable variables.**/
};

/** Transition system.**/
struct XnSys
{
    TableT(XnPcSymm) pcsymms; /**< Process symmetries.**/
    TableT(XnPc) pcs; /**< Process instances.**/
    TableT(XnVbl) vbls;
    BitTable legit;
    TableT(XnRule) legit_rules;
    XnSz nstates; /**< Same as /legit.sz/.**/
    XnSz n_rule_steps;
    /** Allow new transitions in the set of legitimate states.**/
    bool syn_legit;
};
#define DEFAULT_XnSys \
{ DEFAULT_Table, DEFAULT_Table, DEFAULT_Table, \
  DEFAULT_BitTable, \
  DEFAULT_Table, \
  0, 0, false \
}

XnVblSymm
cons2_XnVblSymm (const char* name, XnDomSz domsz);
void
lose_XnVblSymm (XnVblSymm* x);
XnPcSymm
cons1_XnPcSymm (const char* name);
void
lose_XnPcSymm (XnPcSymm* pc);
void
add_vbl_XnPcSymm (XnPcSymm* pc, const char* name, XnDomSz domsz, Bit own);
void
commit_initialization_XnPcSymm (XnPcSymm* pc);

XnVbl
dflt_XnVbl ();
void
lose_XnVbl (XnVbl* x);
XnPc
dflt_XnPc ();
void
lose_XnPc (XnPc* pc);
XnRule
dflt_XnRule ();
XnRule
cons2_XnRule (uint np, uint nq);
XnRule
cons3_XnRule (uint pcidx, uint np, uint nq);
XnRule
dup_XnRule (const XnRule* src);
void
lose_XnRule (XnRule* g);
XnSys
dflt_XnSys ();
void
lose_XnSys (XnSys* sys);
TableT(uint)
wvbls_XnPc (const XnPc* pc);
TableT(uint)
rvbls_XnPc (const XnPc* pc);
TableT(uint)
wpcs_XnVbl (XnVbl* x);
TableT(uint)
rpcs_XnVbl (XnVbl* x);
XnSz
size_XnSys (const XnSys* sys);

#if 0
uint
add_pc_XnSys (XnSys* sys, uint pcsymm_idx);
#endif
void
assoc_XnSys (XnSys* sys, uint pc_idx, uint vbl_idx, Trit mode);
void
commit_initialization_XnPcSymm (XnPcSymm* pc);
void
accept_topology_XnSys (XnSys* sys);
void
statevs_of_XnSys (TableT(XnDomSz)* t, const XnSys* sys, XnSz sidx);
void
oput_XnEVbl (OFile* of, const XnEVbl* ev, const char* delim);
void
rule_XnSys (XnRule* g, const XnSys* sys, XnSz idx);
XnSz
step_XnRule (const XnRule* g, const XnSys* sys);

#endif

