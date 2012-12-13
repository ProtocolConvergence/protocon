
#include "promela.hh"
#include "xnsys.hh"

static
  void
OPutPromelaSelect(ostream& of, const XnVbl& x)
{
  of << "if\n";
  for (uint i = 0; i < x.domsz; ++i) {
    of << ":: true -> " << x.name << "=" << i << ";\n";
  }
  of << "fi;\n";
}

static
  void
OPutPromelaPc(ostream& of, const XnSys& sys, uint pcIdx)
{
  of << "proctype P" << pcIdx << " ()\n{\n";
  bool found = false;

  const XnNet& topo = sys.topology;
  for (uint i = 0; i < sys.actions.size(); ++i) {
    if (topo.actionPcIdx(sys.actions[i]) == pcIdx) {
      found = true;
    }
  }
  if (!found) {
    of << "skip;\n}\n\n";
    return;
  }

  of << "end_" << pcIdx << ":\n";
  of << "do\n";
  for (uint i = 0; i < sys.actions.size(); ++i) {
    const XnAct& act = topo.action(sys.actions[i]);
    if (act.pcIdx == pcIdx) {
      of << ":: atomic {";
      OPut(of, act, topo);
      of << "};\n";
    }
  }
  of << "od;\n" << "}\n\n";
}

/** Output a Promela model for a system.
 *
 * The SPIN model checker can be used to verify that the
 * system is self-stabilizing.
 **/
  void
OPutPromelaModel(ostream& of, const XnSys& sys)
{
  of <<  "/*** Use acceptance cycle check with the LTL claim for a full verification!"
    << "\n *** Assertions, end states, and progress conditions are present to help debugging."
    << "\n *** A safety check and liveness check (BOTH WITH LTL CLAIM DISABLED) should be"
    << "\n *** equivalent to verifying the LTL claim holds via the acceptance cycle check."
    << "\n ***/"
    << "\nbool Legit = false;"
    << "\n";
  const XnNet& topo = sys.topology;
  for (uint pcIdx = 0; pcIdx < topo.pcs.size(); ++pcIdx) {
    const XnPc& pc = topo.pcs[pcIdx];
    for (uint i = 0; i < pc.wvbls.size(); ++i) {
      const XnVbl& x = pc.wvbls[i];
      if (x.domsz <= 2) {
        of << "bit";
      }
      else {
        of << "byte";
      }
      of << ' ' << x.name << ";\n";
    }
  }

  for (uint i = 0; i < topo.pcs.size(); ++i)
    OPutPromelaPc(of, sys, i);

  of << "init {\n";
  for (uint pcIdx = 0; pcIdx < topo.pcs.size(); ++pcIdx) {
    const XnPc& pc = topo.pcs[pcIdx];
    for (uint i = 0; i < pc.wvbls.size(); ++i) {
      const XnVbl& x = pc.wvbls[i];
      OPutPromelaSelect(of, x);
    }
  }

  for (uint i = 0; i < topo.pcs.size(); ++i) {
    of << "run P" << i << "();\n";
  }

  of << "if\n";
  topo.oput(of, sys.invariant, ":: ", " -> skip;\n");
  of << "fi;\n";

  of << "Legit = true;\n";
  of << "progress: skip;\n";

  of << "end:\n";
  of << "if\n";

  topo.oput(of, ~sys.invariant, ":: ", " -> skip;\n");
  of << "fi;\n";
  of << "Legit = false;\n";
  of << "assert(0);\n";
  of << "}\n";

  of << "ltl {\n";
  of << "<> Legit && [] (Legit -> [] Legit)\n";
  of << "}\n";
}

