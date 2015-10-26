

    void
oput_dimacs_CnfFmla (OFile* of, const CnfFmla* fmla)
{
  CnfDisj clause[] = default;
  printf_OFile (of, "p cnf %u %u\n",
                (uint) fmla->nvbls,
                (uint) fmla->idcs.sz);
  {:for (i ; fmla->idcs.sz)
    clause_of_CnfFmla (clause, fmla, i);
    {:for (j ; clause->lits.sz)
      if (!clause->lits.s[j].val)
        oput_char_OFile (of, '-');
      oput_uint_OFile (of, 1+clause->lits.s[j].vbl);
      oput_char_OFile (of, ' ');
    }
    oput_cstr_OFile (of, "0\n");
  }
  lose_CnfDisj (clause);
}

    void
xget_dimacs_result (XFile* xf, bool* sat, BitTable evs)
{
    const char* line = getline_XFile (xf);
    wipe_BitTable (evs, 0);
    if (!line)
    {
        *sat = false;
        DBog0( "No output!" );
        return;
    }
    if (0 == strcmp (line, "UNSAT") ||
        0 == strcmp (line, "unsat"))
    {
        *sat = false;
    }
    else
    {
        int v;
        bool good;
        *sat = true;

        good = xget_int_XFile (xf, &v);
        while (good)
        {
            if      (v > 0)  set1_BitTable (evs, +v-1);
            else if (v < 0)  set0_BitTable (evs, -v-1);
            good = xget_int_XFile (xf, &v);
        }
    }
}

/**
 * Use an external SAT solver to solve /fmla/.
 * If /\ref SatSolve_Z3==true/, use Z3.
 * Otherwise, use MiniSat.
 *
 * \param fmla  CNF formula to solve. This is freed before the solver is run!
 * \param sat   Result. Whether formula is satisfiable.
 * \param evs   Result. Satisfying valuation. This should be allocated to the
 * proper size!
 **/
    void
extl_solve_CnfFmla (CnfFmla* fmla, bool* sat, BitTable evs)
{
  DeclLegit( good );
  OSPc ospc[] = default;
  OFileB ofb[] = default;
  XFileB xfb[] = default;

    *sat = false;

    open_FileB (&ofb->fb, 0, "sat.in");
    oput_dimacs_CnfFmla (&ofb->of, fmla);
    close_OFileB (ofb);

    lose_CnfFmla (fmla);
    *fmla = dflt_CnfFmla ();

    if (SatSolve_Z3)
    {
        stdopipe_OSPc (ospc);
        ospc->cmd = cons1_AlphaTab ("z3");
        PushTable( ospc->args, cons1_AlphaTab ("-dimacs") );
        PushTable( ospc->args, cons1_AlphaTab ("sat.in") );
    }
    else
    {
        ospc->cmd = cons1_AlphaTab ("minisat");
        PushTable( ospc->args, cons1_AlphaTab ("-verb=0") );
        PushTable( ospc->args, cons1_AlphaTab ("sat.in") );
        PushTable( ospc->args, cons1_AlphaTab ("sat.out") );
    }

    DoLegitLine( "spawning solver" )
      spawn_OSPc (ospc);

    DoLegit( 0 )
    {
      if (SatSolve_Z3)
      {
        xget_dimacs_result (ospc->xf, sat, evs);
      }
      else
      {
        close_OSPc (ospc);
        open_FileB (&xfb->fb, 0, "sat.out");
        xget_dimacs_result (&xfb->xf, sat, evs);
      }
    }

    lose_OFileB (ofb);
    lose_XFileB (xfb);
    lose_OSPc (ospc);
}

