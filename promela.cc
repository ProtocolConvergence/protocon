
#include "promela.hh"
#include "xnsys.hh"

static
  void
OPutPromelaVblRef(ostream& of, const Xn::VblSymm& vbl_symm, const Xn::NatMap& index_map)
{
  uint mod_val = 0;
  uint add_val = 0;
  for (uint i = 0; i < index_map.membs.sz(); ++i) {
    if (index_map.membs[i] < 0) {
      mod_val = vbl_symm.membs.sz();
      while (index_map.membs[i] + (int) add_val < 0) {
        add_val += mod_val;
      }
    }
    if (index_map.membs[i] >= (int) vbl_symm.membs.sz()) {
      mod_val = vbl_symm.membs.sz();
    }
  }
  of << vbl_symm.spec->name << "[";
  if (mod_val > 0) {
    of << "(";
  }
  of << index_map.expression;
  if (mod_val > 0) {
    if (add_val > 0) {
      of << "+" << add_val;
    }
    of << ")%" << mod_val;
  }
  of << "]";
}

static
  ostream&
OPutPromelaAction(ostream& of, const Xn::ActSymm& act)
{
  const Xn::PcSymm& pc_symm = *act.pc_symm;
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (i != 0)  of << " && ";
    OPutPromelaVblRef(of, *pc_symm.rvbl_symms[i], pc_symm.rindices[i]);
    of << "==" << act.guard(i);
  }
  of << " ->";
  for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    of << ' ';
    OPutPromelaVblRef(of, *pc_symm.wvbl_symms[i], pc_symm.windices[i]);
    of << "=" << act.assign(i) << ';';
  }
  return of;
}

static
  void
OPutPromelaSelect(ostream& of, const Xn::Vbl& x)
{
#if 0
  of << "  if\n";
  for (uint i = 0; i < x.symm->domsz; ++i) {
    of << "  :: " << x.symm->spec->name
      << "[" << x.symm_idx << "] = " << i << ";\n";
  }
  of << "  fi;\n";
#else
  of << "  if";
  for (uint i = 0; i < x.symm->domsz; ++i) {
    of << " :: " << x.symm->spec->name
      << "[" << x.symm_idx << "] = " << i << ";";
  }
  of << " fi;\n";
#endif
}

static
  void
OPutPromelaPc(ostream& of, const Xn::PcSymm& pc_symm, const Cx::Table<Xn::ActSymm>& acts)
{
  const Xn::PcSymmSpec& pc_symm_spec = *pc_symm.spec;
  of << "proctype " << pc_symm_spec.name
    << "(int " << pc_symm_spec.idx_name << ")\n{\n";

  // Return early if there are no puppet actions.
  {
    bool have_actions = false;
    for (uint i = 0; i < acts.sz(); ++i) {
      if (acts[i].pc_symm == &pc_symm) {
        have_actions = true;
        break;
      }
    }
    if (!have_actions)
      return;
  }

  for (uint i = 0; i < pc_symm_spec.let_map.keys.sz(); ++i) {
    of << "#define " << pc_symm_spec.let_map.keys[i];
    of << " (" << pc_symm_spec.let_map.vals[i].expression;
    of << ")\n";
  }
  of << "end_" << pc_symm_spec.name << ":\n";
  of << "  do\n";
  for (uint i = 0; i < acts.sz(); ++i) {
    const Xn::ActSymm& act = acts[i];
    if (act.pc_symm == &pc_symm) {
      of << "  :: atomic { ";
      OPutPromelaAction(of, act);
      of << " }\n";
    }
  }
  of << "  od;\n";
  for (uint i = 0; i < pc_symm_spec.let_map.keys.sz(); ++i) {
    of << "#undef " << pc_symm_spec.let_map.keys[i] << "\n";
  }
  of << "}\n\n";
}

/** Output a Promela model for a system.
 *
 * The SPIN model checker can be used to verify that the
 * system is self-stabilizing.
 **/
  void
OPutPromelaModel(ostream& of, const Xn::Sys& sys)
{
  const Xn::Net& topo = sys.topology;
  const Xn::Spec& spec = *sys.spec;
  for (uint i = 0; i < spec.constant_map.keys.sz(); ++i) {
    of << "#define " << spec.constant_map.keys[i];
    of << " (" << spec.constant_map.vals[i].expression;
    of << ")\n";
  }
  for (uint i = 0; i < topo.vbl_symms.sz(); ++i) {
    const Xn::VblSymm& x = topo.vbl_symms[i];
    of << (x.domsz == 2 ? "bit" : "byte")
      << " " << x.spec->name << "[" << x.membs.sz() << "];\n";
  }
  of << '\n';

  of << "// Just in case you use the if/then/else construct from {protocon}\n"
    << "#define if\n" << "#define then ->\n" << "#define else :\n";
  of << '\n';

  Cx::Table<Xn::ActSymm> acts;
  const vector<uint>& actions = sys.actions;
  for (uint i = 0; i < actions.size(); ++i) {
    for (uint j = 0; j < topo.represented_actions[actions[i]].sz(); ++j) {
      topo.action(acts.grow1(), topo.represented_actions[actions[i]][j]);
    }
  }
  for (uint i = 0; i < topo.pc_symms.sz(); ++i) {
    OPutPromelaPc(of, topo.pc_symms[i], acts);
  }
  of << "#undef if\n" << "#undef then\n" << "#undef else\n";
  of << '\n';

  of << "init {\n";
  of << "  atomic{//Begin atomic initialization.\n";
  for (uint i = 0; i < topo.vbls.sz(); ++i) {
    OPutPromelaSelect(of, topo.vbls[i]);
  }

  for (uint i = 0; i < topo.pc_symms.sz(); ++i) {
    const Xn::PcSymm& pc_symm = topo.pc_symms[i];
    of << " ";
    for (uint j = 0; j < pc_symm.membs.sz(); ++j) {
      of << " run " << pc_symm.spec->name << "(" << j << ");";
    }
    of << "\n";
  }
  of << "  }//End atomic initialization.\n";

#if 0
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
#endif
  of << "}\n\n";

  //of << "ltl {\n";
  //of << "<> Legit && [] (Legit -> [] Legit)\n";
  //of << "}\n";
}

