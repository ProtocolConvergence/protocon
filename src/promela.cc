
#include "promela.hh"
#include "xnsys.hh"

#include "namespace.hh"

static
  void
OPutPromelaVblRef(std::ostream& of, const Xn::VblSymm& vbl_symm, const Xn::NatMap& index_map,
                  std::string_view index_expression)
{
  uint mod_val = 0;
  uint add_val = 0;
  for (unsigned i = 0; i < index_map.size(); ++i) {
    if (index_map.at(i) < 0) {
      mod_val = vbl_symm.membs.sz();
      while (index_map.at(i) + (int) add_val < 0) {
        add_val += mod_val;
      }
    }
    if (index_map.at(i) >= (int) vbl_symm.membs.sz()) {
      mod_val = vbl_symm.membs.sz();
    }
  }
  of << vbl_symm.spec->name << "[";
  if (mod_val > 0) {
    of << "(";
  }
  of << index_expression;
  if (mod_val > 0) {
    if (add_val > 0) {
      of << "+" << add_val;
    }
    of << ")%" << mod_val;
  }
  of << "]";
}

static
  void
OPutPromelaAction(std::ostream& of, const Xn::ActSymm& act)
{
  const Xn::PcSymm& pc_symm = *act.pc_symm;
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (i != 0)  of << " && ";
    OPutPromelaVblRef(of, *pc_symm.rvbl_symms[i], pc_symm.vbl_indices[i],
                      pc_symm.spec->access[i].index_expression());
    of << "==" << act.guard(i);
  }
  of << " ->";
  for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    of << ' ';
    OPutPromelaVblRef(of, *pc_symm.wvbl_symms[i],
                      pc_symm.vbl_indices[pc_symm.spec->wmap[i]],
                      pc_symm.spec->waccess(i).index_expression());
    of << "=" << act.assign(i) << ';';
  }
}

static
  void
OPutPromelaSelect(std::ostream& ofile, const Xn::Vbl& x)
{
  ofile << "\n  if";
  for (uint i = 0; i < x.symm->domsz; ++i) {
    ofile
      << " :: " << x.symm->spec->name
      << "[" << x.symm_idx << "] = " << i << ";";
  }
  ofile << " fi;";
}

static
  void
OPutPromelaPc(std::ostream& ofile, const Xn::PcSymm& pc_symm, const Table<Xn::ActSymm>& acts,
              const Xn::PcSymm& o_pc_symm, uint pcidx_offset)
{
  const Xn::PcSymmSpec& pc_symm_spec = *pc_symm.spec;
  if (o_pc_symm.membs.empty_ck())
    return;

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

  ofile << '\n'
    << "\nactive [" << o_pc_symm.membs.sz() << "] proctype "
    << pc_symm_spec.name << "()"
    << "\n{"
    ;
  if (!pc_symm_spec.idxmap_name.empty()) {

    ofile
      << "\n#define " << pc_symm_spec.idxmap_name
      << " (_pid - " << pcidx_offset << ")"
      << "\n  int " << pc_symm_spec.idx_name
      << " = " << pc_symm_spec.idxmap_expression << ";"
      << "\n#undef " << pc_symm_spec.idxmap_name
      ;
  }
  else {
    ofile
      << "\n  int " << pc_symm_spec.idx_name
      << " = _pid - " << pcidx_offset
      << ";";
  }
  ofile << "\n  (initialized==1);";

  for (uint i = 0; i < pc_symm_spec.let_map.keys.size(); ++i) {
    ofile
      << "\n#define " << pc_symm_spec.let_map.keys[i]
      << " (" << pc_symm_spec.let_map.vals[i].expression() << ")"
      ;
  }
  ofile << "\nend_" << pc_symm_spec.name << ":";
  ofile << "\n  do";
  for (const Xn::ActSymm& act : acts) {
    if (act.pc_symm == &pc_symm) {
      Xn::ActSymm tmp_act = act;
      tmp_act.pc_symm = &o_pc_symm;
      ofile << "\n  :: atomic { ";
      OPutPromelaAction(ofile, tmp_act);
      ofile << " }";
    }
  }
  ofile << "\n  od;";
  for (const auto& k : pc_symm_spec.let_map.keys) {
    ofile << "\n#undef " << k;
  }
  ofile << "\n}";
}

/** Output a Promela model for a system.
 *
 * The SPIN model checker can be used to verify that the
 * system is self-stabilizing.
 **/
  void
OPutPromelaModel(std::ostream& ofile, const Xn::Sys& sys, const Xn::Net& otopology)
{
  const Xn::Net& topo = sys.topology;
  const Xn::Spec& spec = *otopology.spec;
  for (unsigned i = 0; i < spec.constant_map.keys.size(); ++i) {
    ofile << "\n#define " << spec.constant_map.keys[i]
      << " (" << spec.constant_map.vals[i].expression()
      << ")";
  }
  ofile << "\nbit initialized;";
  for (uint i = 0; i < topo.vbl_symms.sz(); ++i) {
    const Xn::VblSymm& x = otopology.vbl_symms[i];
    ofile << "\n" <<  (x.domsz == 2 ? "bit" : "byte")
      << " " << x.spec->name << "[" << x.membs.sz() << "];";
  }
  ofile << '\n'
    << "\ninit {"
    << "\n  atomic{//Begin atomic initialization."
    ;
  for (uint i = 0; i < topo.vbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = otopology.vbl_symms[i];
    for (uint j = 0; j < vbl_symm.membs.sz(); ++j) {
      OPutPromelaSelect(ofile, *vbl_symm.membs[j]);
    }
  }
  ofile
    << "\n  initialized = 1;"
    << "\n  }//End atomic initialization."
    << "\n}"
    ;
#if 0
  ofile << "  if\n";
  topo.oput(ofile, sys.invariant, "  :: ", " -> skip;\n");
  ofile << "  fi;\n";

  ofile << "  Legit = true;\n";
  //ofile << "progress: skip;\n";

  ofile << "end:\n";
  ofile << "  if\n";

  topo.oput(ofile, ~sys.invariant, "  :: ", " -> skip;\n");
  ofile << "  fi;\n";
  ofile << "  Legit = false;\n";
  ofile << "  assert(0);\n";
#endif

  ofile << '\n'
    << "\n// Just in case you use the if/then/else construct from {protocon}."
    << "\n#define if"
    << "\n#define then ->"
    << "\n#define else :"
    ;

  Table<Xn::ActSymm> acts;
  const vector<uint>& actions = sys.actions;
  for (uint i = 0; i < actions.size(); ++i) {
    topo.unroll_action(acts, actions[i]);
  }
  std::sort(acts.begin(), acts.end());
  uint pcidx_offset = 1;
  for (uint i = 0; i < topo.pc_symms.sz(); ++i) {
    OPutPromelaPc(ofile, topo.pc_symms[i], acts, otopology.pc_symms[i], pcidx_offset);
    pcidx_offset += otopology.pc_symms[i].membs.sz();
  }
  ofile << '\n'
    << "\n#undef if"
    << "\n#undef then"
    << "\n#undef else"
    ;

  ofile << '\n'
    << "\n#if 0  /* Write this yourself (the default is a coloring).*/"
    << "\nltl {"
    << "\n  <> [] ("
    ;
  if (topo.vbl_symms.sz() > 0 && topo.vbl_symms[0].membs.sz() > 0) {
    const Xn::VblSymm& x = otopology.vbl_symms[0];
    ofile << x.spec->name << "[0]";
    for (uint i = 1; i < x.membs.sz(); ++i) {
      ofile << "!=" << x.spec->name << "[" << i << "] && "
        << x.spec->name << "[" << i << "]";
    }
    ofile << "!=" << x.spec->name << "[0]";
  }
  ofile << ")"
    << "\n}"
    << "\n#endif"
    ;

  ofile << "\n\n";
}

END_NAMESPACE

