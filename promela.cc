
#include "promela.hh"
#include "xnsys.hh"

static
  ostream&
OPutPromelaAction(ostream& of, const Xn::ActSymm& act)
{
  const Xn::PcSymm& pc = *act.pc_symm;
  of << "/*" << pc.spec->name << "[i]" << "*/ ";
  for (uint i = 0; i < pc.rvbl_symms.sz(); ++i) {
    if (i != 0)  of << " && ";
    of << pc.rvbl_symms[i]->spec->name
      << "[" <<  pc.rindices[i].expression << "]"
      << "==" << act.guard(i);
  }
  of << " ->";
  for (uint i = 0; i < pc.wvbl_symms.sz(); ++i) {
    of << ' ' << pc.wvbl_symms[i]->spec->name
      << "[" << pc.windices[i].expression << "]"
      << "=" << act.assign(i) << ';';
  }
  return of;
}

static
  void
OPutPromelaSelect(ostream& of, const Xn::Vbl& x)
{
  of << "  if\n";
  for (uint i = 0; i < x.symm->domsz; ++i) {
    of << "  :: " << x.symm->spec->name
      << "[" << x.symm_idx << "] = " << i << ";\n";
  }
  of << "  fi;\n";
}

static
  void
OPutPromelaPc(ostream& of, const Xn::Sys& sys, uint pcidx)
{
  const Xn::Net& topo = sys.topology;
  const Xn::PcSymm& pc = topo.pc_symms[pcidx];
  of << "proctype " << pc.spec->name << "(byte i)\n{\n";
  bool found = false;

  for (uint i = 0; i < sys.actions.size(); ++i) {
    if (topo.action_pcsymm_index(sys.actions[i]) == pcidx) {
      found = true;
    }
  }
  if (!found) {
    of << "  skip;\n  }\n\n";
    return;
  }

  of << "end_" << pcidx << ":\n";
  of << "  do\n";
  for (uint i = 0; i < sys.actions.size(); ++i) {
    Xn::ActSymm act;
    topo.action(act, sys.actions[i]);
    if (act.pc_symm == &topo.pc_symms[pcidx]) {
      of << "  :: atomic {";
      OPutPromelaAction(of, act);
      of << "  }\n";
    }
  }
  of << "  od;\n" << "}\n\n";
}

/** Output a Promela model for a system.
 *
 * The SPIN model checker can be used to verify that the
 * system is self-stabilizing.
 **/
  void
OPutPromelaModel(ostream& of, const Xn::Sys& sys)
{
  of <<  "/*** Use a check for assertion violations and invalid end states!"
    << "\n ***/"
    << "\nbool Legit = false;"
    << "\n";
  const Xn::Net& topo = sys.topology;
  for (uint i = 0; i < topo.vbl_symms.sz(); ++i) {
    const Xn::VblSymm& x = topo.vbl_symms[i];
    of << "byte " << x.spec->name << "[" << x.membs.sz() << "];\n";
  }

  for (uint i = 0; i < topo.pc_symms.sz(); ++i) {
    OPutPromelaPc(of, sys, i);
  }

  of << "init {\n";
  for (uint i = 0; i < topo.vbls.sz(); ++i) {
    OPutPromelaSelect(of, topo.vbls[i]);
  }

  for (uint i = 0; i < topo.pc_symms.sz(); ++i) {
    const Xn::PcSymm& pc_symm = topo.pc_symms[i];
    for (uint j = 0; j < pc_symm.membs.sz(); ++j) {
      of << "  run " << pc_symm.spec->name << "(" << j << ");\n";
    }
  }

  of << "  if\n";
  topo.oput(of, sys.invariant, "  :: ", " -> skip;\n");
  of << "  fi;\n";

  of << "  Legit = true;\n";
  //of << "progress: skip;\n";

  of << "end:\n";
  of << "  if\n";

  topo.oput(of, ~sys.invariant, "  :: ", " -> skip;\n");
  of << "  fi;\n";
  of << "  Legit = false;\n";
  of << "  assert(0);\n";
  of << "}\n";

  //of << "ltl {\n";
  //of << "<> Legit && [] (Legit -> [] Legit)\n";
  //of << "}\n";
}

