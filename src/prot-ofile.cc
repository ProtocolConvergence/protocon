
#include "prot-ofile.hh"

#include "cx/fileb.hh"
#include "pla.hh"
#include "xnsys.hh"

#include "namespace.hh"

static
  void
oput_protocon_constants (OFile& of, const Xn::Spec& spec)
{
  for (uint i = 0; i < spec.constant_map.keys.sz(); ++i) {
    of << "\nconstant " << spec.constant_map.keys[i];
    of << " := " << spec.constant_map.vals[i].expression;
    of << ";";
  }
}

static
  void
oput_protocon_pc_lets (OFile& of, const Xn::PcSymm& pc_symm)
{
  for (uint i = 0; i < pc_symm.spec->let_map.keys.sz(); ++i) {
    of << "\n  let " << pc_symm.spec->let_map.keys[i];
    of << " := " << pc_symm.spec->let_map.vals[i].expression;
    of << ";";
  }
}

static
  void
oput_protocon_pc_predicates (OFile& ofile, const Xn::PcSymm& pc_symm)
{
  for (uint i = 0; i < pc_symm.predicate_map.keys.sz(); ++i) {
    ofile << "\n  predicate "
      << pc_symm.predicate_map.keys[i]
      << " := " << pc_symm.predicate_map.vals[i].expression
      << ";"
      ;
  }
}

static
  const char*
string_of_access_type (Xn::VariableAccessType type)
{
  switch (type) {
    case Xn::ReadAccess:
      return "read";
    case Xn::WriteAccess:
      return "write";
    case Xn::YieldAccess:
      return "yield";
    case Xn::EffectAccess:
      return "effect";
    case Xn::RandomReadAccess:
      return "random read";
    case Xn::RandomWriteAccess:
      return "random write";
    case Xn::NVariableAccessTypes:
      Claim( 0 );
  }
  return 0;
}

static
  void
oput_protocon_pc_vbl (OFile& ofile, const Xn::PcSymm& pc_symm,
                       uint vidx, const String& idxname)
{
  const Xn::VblSymmAccessSpec& access = pc_symm.spec->access[vidx];
  ofile
    << string_of_access_type (access.type) << ": "
    << access.vbl_symm->name << "[" << idxname << "];";
}

static
  void
oput_protocon_pc_vbls (OFile& ofile, const Xn::PcSymm& pc_symm)
{
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    bool symmetric_link_case = false;
    for (uint j = 0; j < pc_symm.spec->link_symmetries.sz(); ++j) {
      const Xn::LinkSymmetry& link_symmetry = pc_symm.spec->link_symmetries[j];
      if (link_symmetry.elem_ck(i)) {
        ofile << "\n  symmetric " << link_symmetry.let_expression
          << " <- {# " << link_symmetry.multiset_expression << " #}"
          << "\n  {"
          ;
        for (uint v = 0; v < link_symmetry.nvbls; ++v) {
          uint vidx = link_symmetry(v, 0);
          ofile << "\n    ";
          oput_protocon_pc_vbl (ofile, pc_symm, vidx,
                                link_symmetry.index_expressions[v]);
        }
        ofile << "\n  }";
        i += link_symmetry.nlinks * link_symmetry.nvbls - 1;
        symmetric_link_case = true;
        break;
      }
    }
    if (symmetric_link_case)  continue;
    oput_protocon_pc_vbl ((ofile << "\n  "), pc_symm,
                          i, pc_symm.spec->access[i].index_expression);
  }
}

  bool
oput_protocon_pc_act (OFile& of, ::XFile* xf,
                      const Table<String>& guard_vbls,
                      const Table<String>& assign_vbls)
{
  DeclLegit( good );
  bool clause = false;
  of << "\n    ( ";
  for (uint i = 0;
       good && i < (guard_vbls.sz() + assign_vbls.sz());
       ++i)
  {
    const char* tok;
    DoLegitLineP(tok, "read token")
      nextok_XFile (xf, 0, 0);

    uint m = 0;
    Table<uint> vals;
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
  of << " )";
  return good;
}

  void
oput_protocon_pc_act (OFile& of, const Xn::ActSymm& act)
{
  of << "\n    ( ";
  const Xn::PcSymm& pc_symm = *act.pc_symm;

  bool need_delim = false;
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (!pc_symm.spec->access[i].synt_read_ck())
      continue;

    if (need_delim)
      of << " && ";
    else
      need_delim = true;
    of << pc_symm.vbl_name(i) << "==" << act.guard(i);
  }
  of << " --> ";
  bool puppet_self_loop = act.puppet_self_loop_ck();
  for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.wvbl_symms[i];
    if (puppet_self_loop && !vbl_symm.pure_shadow_ck())
      continue;
    if (vbl_symm.domsz == act.assign(i))
      continue;
    of << pc_symm.vbl_name(pc_symm.spec->wmap[i]) << ":=";
    if (pc_symm.spec->waccess(i).random_write_ck())
      of << "_; ";
    else
      of << act.assign(i) << "; ";
  }
  of << ")";
}

  bool
oput_protocon_pc_acts (OFile& of, const Xn::PcSymm& pc_symm,
                       const Table<Xn::ActSymm>& acts,
                       bool use_espresso)
{
  DeclLegit( good );
  const Xn::PcSymmSpec& pc_symm_spec = *pc_symm.spec;
  if (pc_symm_spec.shadow_act_strings.sz() > 0) {
    of << "\n  shadow:";
    for (uint i = 0; i < pc_symm_spec.shadow_act_strings.sz(); ++i) {
      of << "\n    ( " << pc_symm_spec.shadow_act_strings[i] << " )";
    }
    of << "\n    ;";
  }
  if (pc_symm_spec.permit_act_strings.sz() > 0) {
    of << "\n  permit:";
    for (uint i = 0; i < pc_symm_spec.permit_act_strings.sz(); ++i) {
      of << "\n    ( " << pc_symm_spec.permit_act_strings[i] << " )";
    }
    of << "\n    ;";
  }
  if (pc_symm_spec.forbid_act_strings.sz() > 0) {
    of << "\n  forbid:";
    for (uint i = 0; i < pc_symm_spec.forbid_act_strings.sz(); ++i) {
      of << "\n    ( " << pc_symm_spec.forbid_act_strings[i] << " )";
    }
    of << "\n    ;";
  }

  for (uint i = 0; i < pc_symm.conflicts.sz(); ++i) {
    of << "\n  conflict:";
    const FlatSet<Xn::ActSymm>& conflict = pc_symm.conflicts[i];
    for (uint j = 0; j < conflict.sz(); ++j) {
      oput_protocon_pc_act (of, conflict[j]);
    }
    of << "\n    ;";
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

  of << "\n  puppet:";

  if (use_espresso) {
    DoLegitLine( "" )
      oput_protocon_pc_acts_espresso (of, pc_symm, acts);
  }
  else {
    for (uint i = 0; i < acts.sz(); ++i) {
      if (acts[i].pc_symm == &pc_symm) {
        oput_protocon_pc_act (of, acts[i]);
      }
    }
  }

  of << "\n    ;";
  return good;
}

static
  bool
oput_protocon_pc_assume (OFile& of, const Xn::PcSymm& pc_symm)
{
  const String& assume_expression = pc_symm.spec->closed_assume_expression;
  if (assume_expression.empty_ck())
    return true;
  of << "\n  (assume & closed)\n    (" << assume_expression << ");";
  return true;
}

static
  String
string_of_invariant_style (Xn::InvariantStyle style, Xn::InvariantScope scope)
{
  String s = "";
  const char* pfx = "";
  const char* sfx = "";

  switch (scope)
  {
    case Xn::DirectInvariant:
      break;
    case Xn::ShadowInvariant:
      s = "(";
      sfx = " % puppet)";
      break;
    case Xn::FutureInvariant:
      pfx = "future ";
      break;
    case Xn::NInvariantScopes:
      Claim( 0 );
  }

  s << "(future & " << pfx;
  switch (style)
  {
    case Xn::FutureAndClosed:
      s << "closed";
      break;
    case Xn::FutureAndSilent:
      s << "silent";
      break;
    case Xn::FutureAndShadow:
      s << "shadow";
      break;
    case Xn::FutureAndActiveShadow:
      s << "active shadow";
      break;
    case Xn::NInvariantStyles:
      Claim( 0 );
  }
  s << ")" << sfx;
  return s;
}

static
  const char*
string_of_invariant_behav (Xn::InvariantBehav behav)
{
  switch (behav)
  {
    case Xn::FutureSilent:
      return "future silent";
    case Xn::FutureActiveShadow:
      return "future active shadow";
    case Xn::FutureShadow:
    case Xn::NInvariantBehavs:
      return 0;
  }
  return 0;
}

static
  bool
oput_protocon_pc_invariant (OFile& of, const Xn::PcSymm& pc_symm,
                            const String& style_str)
{
  const String& invariant_expression = pc_symm.spec->invariant_expression;
  if (invariant_expression.empty_ck())
    return true;

  of << "\n  " << style_str
    << "\n    (" << invariant_expression << ");";
  return true;
}

  bool
oput_protocon_file (OFile& of, const Xn::Sys& sys,
                    const Xn::Net& o_topology,
                    const vector<uint>& actions,
                    bool use_espresso,
                    const char* comment)
{
  DeclLegit( good );

  const Xn::Net& topo = sys.topology;
  if (comment) {
    of << "// " << comment;
  }
  oput_protocon_constants (of, *o_topology.spec);
  for (uint i = 0; i < topo.vbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = topo.vbl_symms[i];
    of << '\n';
    if (vbl_symm.pure_shadow_ck())
      of << "shadow ";
    else if (vbl_symm.pure_puppet_ck())
      of << "puppet ";

    of << "variable " << vbl_symm.spec->name
      << "[" << vbl_symm.spec->nmembs_expression
      << "] < " << vbl_symm.spec->domsz_expression << ";";
  }

  for (uint i = 0; i < sys.predicate_map.sz(); ++i) {
    of << "\npredicate " << sys.predicate_map.keys[i]
      << " :=\n  " << sys.predicate_map.expressions[i] << ";";
  }

  if (!!sys.spec->closed_assume_expression) {
    of << "\n(assume & closed)\n  (" << sys.spec->closed_assume_expression << ")\n  ;";
  }

  String style_str =
    string_of_invariant_style (sys.spec->invariant_style,
                               sys.spec->invariant_scope);
  if (!sys.spec->invariant_expression.empty_ck()) {
    String legit_str = sys.spec->invariant_expression;
    of << "\n" << style_str << "\n  (" << legit_str << ")\n  ;";
  }

  if (sys.spec->invariant_behav != Xn::FutureShadow &&
      sys.spec->invariant_behav != Xn::NInvariantBehavs) {
    of << "\n" << string_of_invariant_behav (sys.spec->invariant_behav) << ";";
  }


  Table<Xn::ActSymm> acts;
  for (uint i = 0; i < actions.size(); ++i) {
    for (uint j = 0; j < sys.topology.represented_actions[actions[i]].sz(); ++j) {
      sys.topology.action(acts.grow1(), sys.topology.represented_actions[actions[i]][j]);
    }
  }
  std::sort(acts.begin(), acts.end());

  for (uint i = 0; i < sys.topology.pc_symms.sz(); ++i) {
    const Xn::PcSymm& pc_symm = sys.topology.pc_symms[i];
    if (pc_symm.membs.sz() == 0)  continue;

    of << "\nprocess " << pc_symm.spec->name
      << "[" << pc_symm.spec->idx_name
      ;
    if (!!pc_symm.spec->idxmap_name) {
      of << " <- map " << pc_symm.spec->idxmap_name
        << " < " << o_topology.pc_symms[i].spec->nmembs_expression
        << " : " << pc_symm.spec->idxmap_expression;
    }
    else {
      of << " < " << o_topology.pc_symms[i].spec->nmembs_expression;
    }
    of << "]" << "\n{";
    oput_protocon_pc_lets (of, pc_symm);
    oput_protocon_pc_vbls (of, pc_symm);
    oput_protocon_pc_predicates (of, pc_symm);
    DoLegitLine("output assume")
      oput_protocon_pc_assume (of, pc_symm);
    DoLegitLine("output invariant")
      oput_protocon_pc_invariant (of, pc_symm, style_str);
    DoLegitLine("output actions")
      oput_protocon_pc_acts (of, pc_symm, acts, use_espresso);
    of << "\n}\n";
  }

  return good;
}

  bool
oput_protocon_file (OFile& of, const Xn::Sys& sys, const vector<uint>& actions,
                    bool use_espresso, const char* comment)
{
  return oput_protocon_file (of, sys, sys.topology, actions, use_espresso, comment);
}

  bool
oput_protocon_file (OFile& of, const Xn::Sys& sys,
                    bool use_espresso, const char* comment)
{
  return oput_protocon_file (of, sys, sys.actions, use_espresso, comment);
}

  bool
oput_protocon_file (const String& ofilename,
                    const Xn::Sys& sys,
                    const Xn::Net& o_topology,
                    const vector<uint>& actions,
                    bool use_espresso,
                    const char* comment)
{
  Cx::OFileB ofb;
  OFile ofile = ofb.uopen(ofilename);
  if (!ofile)  return false;
  return oput_protocon_file (ofile, sys, o_topology, actions, use_espresso, comment);
}

  bool
oput_protocon_file (const String& ofilename, const Xn::Sys& sys,
                    bool use_espresso,
                    const char* comment)
{
  return oput_protocon_file (ofilename, sys, sys.topology, sys.actions, use_espresso, comment);
}

END_NAMESPACE

