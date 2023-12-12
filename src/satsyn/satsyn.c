/**
 * \file satsyn.c
 *
 * SAT-based stabilization synthesis.
 **/
#include "cx/bittable.h"
#include "cx/table.h"

#include <assert.h>
#include <stdio.h>

#include "detect.h"
#include "encodesat.h"
#include "instance.h"
#include "promela.h"
#include "synsearch.h"
#include "xnsys.h"

#include "src/inline/eq_cstr.h"
static inline
bool eql_cstr(const char* a, const char* b) {return eq_cstr(a, b);}

/** Use Z3 instead of MiniSat.**/
static bool SatSolve_Z3 = false;



static inline
  void
oput_BitTable(FildeshO* out, const BitTable bt)
{
  for (size_t i = 0; i < bt.sz; ++i) {
    putc_FildeshO(out, test_BitTable (bt, i) ? '1' : '0');
  }
}


#include "inst-sat3.h"

/**
 * Reduce the AddConvergence problem to SAT and solve it.
 *
 * TODO: Make this work when the protocol has
 * transitions defined in the legit states.
 **/
    void
synsearch_sat (FMem_synsearch* tape)
{
  CnfFmla fmla[] = {DEFAULT_CnfFmla};
  *fmla = encode_sat(tape);
  if (fmla->nvbls == 0) {
    lose_CnfFmla(fmla);
    return;
  }
  else {
    BitTable evs = cons2_BitTable (fmla->nvbls, 0);
    TableT(XnSz)* may_rules = TopTable( tape->may_rules );
    XnRule* g = TopTable( tape->rules );
    bool sat = false;
    extl_solve_CnfFmla (fmla, &sat, evs);
    if (0) {
      FildeshO* out = open_FildeshOF("/dev/stderr");
      oput_BitTable(out, evs);
      putc_FildeshO(out, '\n');
      close_FildeshO(out);
    }

    tape->stabilizing = sat;
    if (sat)
      for (unsigned i = 0; i < may_rules->sz; ++i) {
        if (test_BitTable(evs, i)) {
          rule_XnSys(g, tape->sys, may_rules->s[i]);
          add_XnRule(tape, g);
          g = grow1_rules_synsearch(tape);
        }
      }
    lose_BitTable(&evs);
  }
  -- tape->rules.sz;

  lose_CnfFmla(fmla);
}

#include "pla.h"

    int
main (int argc, char** argv)
{
    int argi = 1;
    XnSysInstance inst_kind =
        /* Sat3Inst */
        /* Sat3RingInst */
        /* Sat3RingWSatInst */
        /* MatchingInst */
        ColoringInst
        /* TokenRing3BitInst */
        /* TokenRingDijkstraInst */
        /* TokenRingDijkstra4StateInst */
        ;
    bool use_synsearch_sat = false;
    uint n_ring_pcs = 6;  /* For rings (excluding 3-SAT rings).*/
    const uint domsz = 3;
    const bool manual_soln = true;
    XnSys sys[] = {DEFAULT_XnSys};
    CnfFmla fmla[] = {DEFAULT_CnfFmla};
    BoolLit clauses[][3] = {
#if 0
#elif 1
        {{Yes, 0}, {Yes, 1}, {Yes, 0}},
        {{Yes, 1}, {Nil, 0}, {Yes, 1}},
        {{Yes, 1}, {Yes, 1}, {Nil, 1}},
        {{Yes, 2}, {Yes, 1}, {Nil, 2}},
        {{Nil, 2}, {Nil, 2}, {Yes, 3}},
        {{Nil, 0}, {Nil, 0}, {Nil, 0}}
#elif 0
        {{Nil, 0}, {Nil, 0}, {Nil, 0}}
#elif 0
        {{Yes, 1}, {Nil, 1}, {Yes, 0}},
        {{Nil, 0}, {Nil, 0}, {Nil, 0}}
#elif 0
        /* No solution, but not super trivial.*/
        {{Yes, 1}, {Yes, 1}, {Yes, 1}},
        {{Nil, 0}, {Nil, 0}, {Nil, 0}},
        {{Yes, 0}, {Nil, 1}, {Nil, 1}}
#endif
    };

    while (argi < argc)
    {
        if (eql_cstr (argv[argi], "-h")) {
           failout_sysCx ("There is no help for you.");
        }
        else if (eql_cstr(argv[argi], "-solver") && eql_cstr(argv[argi+1], "z3")) {
          argi += 1;
          use_synsearch_sat = true;
          SatSolve_Z3 = true;
        }
        else if (eql_cstr(argv[argi], "-solver") && eql_cstr(argv[argi+1], "minisat")) {
          argi += 1;
          use_synsearch_sat = true;
        }
        else if (eql_cstr (argv[argi], "-inst")) {
            bool need_npcs = false;
            ++argi;
            if (eql_cstr (argv[argi], "coloring")) {
                need_npcs = true;
                inst_kind = ColoringInst;
            }
            else if (eql_cstr (argv[argi], "matching")) {
                need_npcs = true;
                inst_kind = MatchingInst;
            }
            else if (eql_cstr (argv[argi], "dijkstra")) {
                need_npcs = true;
                inst_kind = TokenRingDijkstraInst;
            }
            else if (eql_cstr (argv[argi], "dijkstra4state")) {
                need_npcs = true;
                inst_kind = TokenRingDijkstra4StateInst;
            }
            else if (eql_cstr (argv[argi], "bit3")) {
                need_npcs = true;
                inst_kind = TokenRing3BitInst;
            }
            else if (eql_cstr (argv[argi], "sat3")) {
                inst_kind = Sat3Inst;
            }
            else {
                failout_sysCx ("bad -inst");
            }

            ++argi;
            if (need_npcs) {

                if (fildesh_parse_unsigned(&n_ring_pcs, argv[argi])) {
                    ++argi;
                }
                else {
                    failout_sysCx ("bad number of processes");
                }
            }
        }
        else {
            DBog1("arg: %s", argv[argi]);
            failout_sysCx ("Bad argument.");
        }
        ++argi;
    }
    if (argi < argc)
        failout_sysCx ("No arguments expected.");

    for (uint i = 0; i < ArraySz(clauses); ++i) {
        CnfDisj clause = dflt_CnfDisj ();
        for (uint j = 0; j < 3; ++j) {
            PushTable( clause.lits, clauses[i][j] );
            if (clauses[i][j].vbl + 1 > fmla->nvbls )
                fmla->nvbls = clauses[i][j].vbl + 1;
        }
        app_CnfFmla (fmla, &clause);
        lose_CnfDisj (&clause);
    }
    DBog1( "/nvbls==%u/", fmla->nvbls );


    switch (inst_kind)
    {
    case Sat3Inst:
        *sys = inst_sat3_XnSys (fmla);
        break;
    case Sat3RingInst:
        *sys = inst_sat3_ring_XnSys (fmla, false);
        break;
    case Sat3RingWSatInst:
        *sys = inst_sat3_ring_XnSys (fmla, true);
        break;
    case MatchingInst:
        *sys = inst_matching_XnSys (n_ring_pcs);
        break;
    case ColoringInst:
        *sys = inst_coloring_XnSys (n_ring_pcs, domsz);
        break;
    case TokenRing3BitInst:
        *sys = inst_bit3_XnSys (n_ring_pcs);
        break;
    case TokenRingDijkstraInst:
        *sys = inst_dijkstra_XnSys (n_ring_pcs);
        break;
    case TokenRingDijkstra4StateInst:
        *sys = inst_dijkstra4state_XnSys (n_ring_pcs);
        break;
    default:
        failout_sysCx ("Invalid problem instance.");
        break;
    };

    DBog1( "size is %u", (uint) sys->nstates );

    {
        FMem_synsearch tape = cons1_FMem_synsearch (sys);
        if (inst_kind == Sat3Inst ||
            inst_kind == Sat3RingInst ||
            inst_kind == Sat3RingWSatInst)
        {
            bool sat = false;
            BitTable evs = cons2_BitTable (fmla->nvbls, 0);

            extl_solve_CnfFmla (fmla, &sat, evs);
            if (sat)
            {
                DBog1( "Should be satisfiable? %s", sat ? "YES" : "NO" );
                if (manual_soln)
                {
                    if (inst_kind == Sat3Inst)
                        sat3_soln_XnSys (&tape.rules, evs, sys);
                    else if (inst_kind == Sat3RingInst)
                        sat3_ring_soln_XnSys (&tape.rules, evs, sys, fmla);

                    DBog1( "Giving %u hints.", (uint)tape.rules.sz );
                    tape.n_cached_rules = tape.rules.sz;
                }
            }
            lose_BitTable (&evs);
        }

        if (use_synsearch_sat)
            synsearch_sat (&tape);
        else
            synsearch (&tape);

        if (tape.stabilizing)  DBog0( "Solution found! :)" );
        else                   DBog0( "No solution. :(" );

        if (tape.stabilizing)
        {
            Trit stabilizing = detect_strong_convergence (&tape);
            if (stabilizing == Yes)
                DBog0( "Protocol verified, should work." );
            else
                DBog0( "Protocol could not be verified!?" );
        }

        if (tape.stabilizing || (manual_soln && tape.rules.sz > 0))
        {
            // Promela.
            FildeshO* out = open_FildeshOF("model.pml");
            oput_promela(out, sys, tape.rules);
            close_FildeshO(out);

            /* This is just a test, but should be used to
             * minimize the representation for transition rules.
             */
            do_pla_XnSys (sys, tape.rules);
        }

        lose_FMem_synsearch (&tape);
    }

    lose_CnfFmla (fmla);
    lose_XnSys (sys);
    return 0;
}

