
extern "C" {
#include "cx/syscx.h"
}
#include "pla.hh"

extern "C" {
#include "cx/ospc.h"
}

  void
oput_pla_val (Cx::OFile& of, uint j, uint n)
{
  for (uint i = 0; i < n; ++i)
    of << (i == j ? 1 : 0);
}

  void
oput_pla_act (Cx::OFile& of, const Xn::ActSymm& act)
{
  const Xn::PcSymm& pc_symm = *act.pc_symm;
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (pc_symm.rvbl_symms[i]->pure_shadow_ck() && !pc_symm.write_flags[i])
      continue;
    of << ' ';
    oput_pla_val (of, act.guard(i), pc_symm.doms[i]);
  }
  for (uint i = 0; i < pc_symm.wmap.sz(); ++i) {
    of << ' ';
    oput_pla_val (of, act.assign(i), pc_symm.doms[pc_symm.wmap[i]]);
  }
}

  void
oput_pla_pc_acts (Cx::OFile& of, const Xn::PcSymm& pc_symm,
                  const Cx::Table<Xn::ActSymm>& acts)
{
  Claim2( pc_symm.wvbl_symms.sz() ,==, pc_symm.wmap.sz() );

  uint nrvbls = 0;
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (!(pc_symm.rvbl_symms[i]->pure_shadow_ck() && !pc_symm.write_flags[i]))
      nrvbls += 1;
  }

  of << ".mv " << (nrvbls + pc_symm.wmap.sz()) << " 0";
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (pc_symm.rvbl_symms[i]->pure_shadow_ck() && !pc_symm.write_flags[i])
      continue;
    of << ' ' << pc_symm.doms[i];
  }
  for (uint i = 0; i < pc_symm.wmap.sz(); ++i)
    of << ' ' << pc_symm.doms[pc_symm.wmap[i]];
  of << '\n';

  of << '#';
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (pc_symm.rvbl_symms[i]->pure_shadow_ck() && !pc_symm.write_flags[i])
      continue;
    of << ' ' << pc_symm.vbl_name(i);
  }

  for (uint i = 0; i < pc_symm.wmap.sz(); ++i)
    of << ' ' << pc_symm.vbl_name(pc_symm.wmap[i]) << '\'';
  of << '\n';

  for (uint i = 0; i < acts.sz(); ++i) {
    const Xn::ActSymm& act = acts[i];
    if (act.pc_symm == &pc_symm) {
      oput_pla_act (of, act);
      of << '\n';
    }
  }
  of << ".e\n";
}

static
  void
oput_protocon_constants (Cx::OFile& of, const Xn::Spec& spec)
{
  for (uint i = 0; i < spec.constant_map.keys.sz(); ++i) {
    of << "constant " << spec.constant_map.keys[i];
    of << " := " << spec.constant_map.vals[i].expression;
    of << ";\n";
  }
}

static
  void
oput_protocon_pc_lets (Cx::OFile& of, const Xn::PcSymm& pc_symm)
{
  for (uint i = 0; i < pc_symm.spec->let_map.keys.sz(); ++i) {
    of << "  let " << pc_symm.spec->let_map.keys[i];
    of << " := " << pc_symm.spec->let_map.vals[i].expression;
    of << ";\n";
  }
}

static
  void
oput_protocon_pc_vbls (Cx::OFile& of, const Xn::PcSymm& pc_symm)
{
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    bool obliv = false;
    for (uint j = 0; j < pc_symm.spec->oblivious_specs.sz(); ++j) {
      const Xn::ObliviousSpec& obliv_spec = pc_symm.spec->oblivious_specs[j];
      if (obliv_spec.elem_ck(i)) {
        of << "  for " << obliv_spec.let_expression
          << " <- {# " << obliv_spec.multiset_expression << " #}\n";
        of << "  {\n";
        for (uint v = 0; v < obliv_spec.nvbls; ++v) {
          uint vidx = obliv_spec(v, 0);
          of << "    "
            << (pc_symm.write_flags[vidx] ? "write" : "read") << ": "
            << pc_symm.spec->rvbl_symms[vidx]->name
            << "[" << obliv_spec.index_expressions[v] << "];\n";
        }
        of << "  }\n";
        i += obliv_spec.nlinks * obliv_spec.nvbls - 1;
        obliv = true;
        break;
      }
    }
    if (obliv)  continue;
    of << "  " << (pc_symm.write_flags[i] ? "write" : "read") << ": ";
    of << pc_symm.vbl_name(i);
    of << ";\n";
  }
}

  bool
oput_protocon_pc_act (Cx::OFile& of, XFile* xf,
                      const Cx::Table<Cx::String>& guard_vbls,
                      const Cx::Table<Cx::String>& assign_vbls)
{
  Sign good = 1;
  bool clause = false;
  of << "    ( ";
  for (uint i = 0;
       good && i < (guard_vbls.sz() + assign_vbls.sz());
       ++i)
  {
    const char* tok = nextok_XFile (xf, 0, 0);

    DoLegit(good, "read token")
      good = !!tok;

    uint m = 0;
    Cx::Table<uint> vals;
    while (good && tok[m])
    {
      Claim( tok[m] == '0' || tok[m] == '1' );
      if (tok[m] == '1')
        vals.push(m);
      ++ m;
    }

    if (i >= guard_vbls.sz()) {
      if (i == guard_vbls.sz()) {
        of << " -->";
      }
      Claim2( vals.sz() ,==, 1 );
      of << ' ' << assign_vbls[i-guard_vbls.sz()] << ":=" << vals[0] << ';';
      continue;
    }

    if (vals.sz() == m)  continue;

    if (clause)
      of << " && ";
    clause = true;

    if (vals.sz() == m-1 && m > 2) {
      for (uint j = 0; j < m; ++j) {
        if (!vals.elem_ck(j)) {
          of << guard_vbls[i] << "!=" << j;
          break;
        }
      }
      continue;
    }

    if (vals.sz() > 1)  of << "(";
    for (uint j = 0; good && j < vals.sz(); ++j) {
      if (j > 0)  of << " || ";
      of << guard_vbls[i] << "==" << vals[j];
    }
    if (vals.sz() > 1)  of << ")";
  }
  of << " )\n";
  return good;
}

  void
oput_protocon_pc_act (Cx::OFile& of, const Xn::ActSymm& act)
{
  of << "    ( ";
  const Xn::PcSymm& pc_symm = *act.pc_symm;

  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (i > 0) {
      of << " && ";
    }
    of << pc_symm.vbl_name(i) << "==" << act.guard(i);
  }
  of << " --> ";
  for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    of << pc_symm.vbl_name(pc_symm.wmap[i]) << ":=" << act.assign(i) << "; ";
  }
  of << ")\n";
}

  bool
oput_protocon_pc_acts (Cx::OFile& of, const Xn::PcSymm& pc_symm,
                       const Cx::Table<Xn::ActSymm>& acts,
                       OSPc* ospc,
                       bool use_espresso)
{
  Sign good = 1;
  const Xn::PcSymmSpec& pc_symm_spec = *pc_symm.spec;
  if (pc_symm_spec.shadow_act_strings.sz() > 0) {
    of << "  shadow action:\n";
    for (uint i = 0; i < pc_symm_spec.shadow_act_strings.sz(); ++i) {
      of << "    ( " << pc_symm_spec.shadow_act_strings[i] << " )\n";
    }
    of << "    ;\n";
  }
  if (pc_symm_spec.forbid_act_strings.sz() > 0) {
    of << "  forbid action:\n";
    for (uint i = 0; i < pc_symm_spec.forbid_act_strings.sz(); ++i) {
      of << "    ( " << pc_symm_spec.forbid_act_strings[i] << " )\n";
    }
    of << "    ;\n";
  }

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
      return true;
  }

  // Names for variables.
  Cx::Table<Cx::String> guard_vbls;
  Cx::Table<Cx::String> assign_vbls( pc_symm.wmap.sz() );
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (pc_symm.rvbl_symms[i]->pure_shadow_ck() && !pc_symm.write_flags[i])
      continue;
    guard_vbls.push(pc_symm.vbl_name(i));
  }
  for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    assign_vbls[i] = pc_symm.vbl_name(pc_symm.wmap[i]);
  }

  of << "  puppet action:\n";
  if (!use_espresso) {
    for (uint i = 0; i < acts.sz(); ++i) {
      if (acts[i].pc_symm == &pc_symm) {
        oput_protocon_pc_act (of, acts[i]);
      }
    }
    of << "    ;\n";
    return true;
  }

  DoLegit( good, "spawn espresso" )
    good = spawn_OSPc (ospc);

  if (good) {
    Cx::OFile espresso_xf(ospc->of);
    oput_pla_pc_acts (espresso_xf, pc_symm, acts);
    close_OFile (ospc->of);
  }

  while (good && !skip_cstr_XFile (ospc->xf, ".p"))
  {
    DoLegit(good, "get line")
      good = !!getline_XFile (ospc->xf);
  }

  uint n = 0;
  DoLegit(good, "read number of lines from espresso")
    good = xget_uint_XFile (ospc->xf, &n);

  getline_XFile (ospc->xf);

  for (uint i = 0; good && i < n; ++i) {
    XFile olay[1];

    DoLegit(good, "get line from espresso")
      good = getlined_olay_XFile (olay, ospc->xf, "\n");

    DoLegit(good, 0)
      good =
      oput_protocon_pc_act (of, olay, guard_vbls, assign_vbls);
  }
  of << "    ;\n";

  close_OSPc (ospc);
  return good;
}

  bool
oput_protocon_file (Cx::OFile& of, const Xn::Sys& sys, bool use_espresso, const vector<uint>& actions)
{
  Sign good = 1;
  OSPc ospc[1];
  *ospc = dflt_OSPc ();

  stdxpipe_OSPc (ospc);
  stdopipe_OSPc (ospc);
  ospc->cmd = cons1_AlphaTab ("espresso");

  const Xn::Net& topo = sys.topology;
  oput_protocon_constants (of, *sys.spec);
  for (uint i = 0; i < topo.vbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = topo.vbl_symms[i];
    if (vbl_symm.shadow_puppet_role == Xn::Vbl::Shadow)
      of << "shadow\n";
    if (vbl_symm.shadow_puppet_role == Xn::Vbl::Puppet)
      of << "puppet\n";

    of << "variable " << vbl_symm.spec->name
      << "[Nat % " << vbl_symm.spec->nmembs_expression
      << "] <- Nat % " << vbl_symm.spec->domsz_expression << ";\n";
  }

  Cx::Table<Xn::ActSymm> acts;
  for (uint i = 0; i < actions.size(); ++i) {
    for (uint j = 0; j < topo.represented_actions[actions[i]].sz(); ++j) {
      topo.action(acts.grow1(), topo.represented_actions[actions[i]][j]);
    }
  }

  for (uint i = 0; i < topo.pc_symms.sz(); ++i) {
    const Xn::PcSymm& pc_symm = topo.pc_symms[i];
    of << "process " << pc_symm.spec->name
      << "[" << pc_symm.spec->idx_name << " <- Nat % " << pc_symm.spec->nmembs_expression << "]\n";
    of << "{\n";
    oput_protocon_pc_lets (of, pc_symm);
    oput_protocon_pc_vbls (of, pc_symm);
    DoLegit(good, "output actions")
      good = oput_protocon_pc_acts (of, pc_symm, acts, ospc, use_espresso);
    of << "}\n";
  }

  for (uint i = 0; i < sys.predicate_map.sz(); ++i) {
    of << "predicate " << sys.predicate_map.keys[i]
      << " :=\n  " << sys.predicate_map.expressions[i] << ";\n";
  }

  if (sys.direct_invariant_ck())
    of << "direct";
  else
    of << "shadow";

  of << " invariant:\n  " << sys.spec->invariant_expression << "\n  ;\n";

  lose_OSPc (ospc);
  return good;
}

  bool
oput_protocon_file (Cx::OFile& of, const Xn::Sys& sys, bool use_espresso)
{
  return oput_protocon_file (of, sys, use_espresso, sys.actions);
}

