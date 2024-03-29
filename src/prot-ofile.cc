
#include "prot-ofile.hh"

#include <sstream>

#include <fildesh/ostream.hh>

#include "pla.hh"
#include "xnsys.hh"

#include "namespace.hh"

static
  void
oput_protocon_constants(std::ostream& out, const Xn::Spec& spec)
{
  for (uint i = 0; i < spec.constant_map.keys.sz(); ++i) {
    out << "\nconstant " << spec.constant_map.keys[i];
    out << " := " << spec.constant_map.vals[i].expression;
    out << ";";
  }
}

static
  void
oput_protocon_pc_lets(std::ostream& out, const Xn::PcSymm& pc_symm)
{
  for (uint i = 0; i < pc_symm.spec->let_map.keys.sz(); ++i) {
    out << "\n  let " << pc_symm.spec->let_map.keys[i];
    out << " := " << pc_symm.spec->let_map.vals[i].expression;
    out << ";";
  }
}

static
  void
oput_protocon_pc_predicates(std::ostream& ofile, const Xn::PcSymm& pc_symm)
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
string_of_access_type(Xn::VariableAccessType type)
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
oput_protocon_pc_vbl(std::ostream& ofile, const Xn::PcSymm& pc_symm,
                     unsigned vidx, std::string_view idxname)
{
  const Xn::VblSymmAccessSpec& access = pc_symm.spec->access[vidx];
  ofile
    << string_of_access_type (access.type) << ": "
    << access.vbl_symm->name << "[" << idxname << "];";
}

static
  void
oput_protocon_pc_vbls(std::ostream& ofile, const Xn::PcSymm& pc_symm)
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

  void
oput_protocon_pc_act(std::ostream& out, const Xn::ActSymm& act)
{
  out << "\n    ( ";
  const Xn::PcSymm& pc_symm = *act.pc_symm;

  bool need_delim = false;
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (!pc_symm.spec->access[i].synt_read_ck())
      continue;

    if (need_delim)
      out << " && ";
    else
      need_delim = true;
    out << pc_symm.vbl_name(i) << "==" << act.guard(i);
  }
  out << " --> ";
  bool puppet_self_loop = act.puppet_self_loop_ck();
  for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.wvbl_symms[i];
    if (puppet_self_loop && !vbl_symm.pure_shadow_ck())
      continue;
    if (vbl_symm.domsz == act.assign(i))
      continue;
    out << pc_symm.vbl_name(pc_symm.spec->wmap[i]) << ":=";
    if (pc_symm.spec->waccess(i).random_write_ck())
      out << "_; ";
    else
      out << act.assign(i) << "; ";
  }
  out << ")";
}

static
  bool
oput_protocon_pc_acts(std::ostream& out, const Xn::PcSymm& pc_symm,
                      const std::vector<Xn::ActSymm>& acts,
                      std::string_view maybe_espresso)
{
  const Xn::PcSymmSpec& pc_symm_spec = *pc_symm.spec;
  if (pc_symm_spec.shadow_act_strings.sz() > 0) {
    out << "\n  shadow:";
    for (uint i = 0; i < pc_symm_spec.shadow_act_strings.sz(); ++i) {
      out << "\n    ( " << pc_symm_spec.shadow_act_strings[i] << " )";
    }
    out << "\n    ;";
  }
  if (pc_symm_spec.permit_act_strings.sz() > 0) {
    out << "\n  permit:";
    for (uint i = 0; i < pc_symm_spec.permit_act_strings.sz(); ++i) {
      out << "\n    ( " << pc_symm_spec.permit_act_strings[i] << " )";
    }
    out << "\n    ;";
  }
  if (pc_symm_spec.forbid_act_strings.sz() > 0) {
    out << "\n  forbid:";
    for (uint i = 0; i < pc_symm_spec.forbid_act_strings.sz(); ++i) {
      out << "\n    ( " << pc_symm_spec.forbid_act_strings[i] << " )";
    }
    out << "\n    ;";
  }

  for (uint i = 0; i < pc_symm.conflicts.sz(); ++i) {
    out << "\n  conflict:";
    const FlatSet<Xn::ActSymm>& conflict = pc_symm.conflicts[i];
    for (uint j = 0; j < conflict.sz(); ++j) {
      oput_protocon_pc_act (out, conflict[j]);
    }
    out << "\n    ;";
  }

  // Return early if there are no puppet actions.
  {
    bool have_actions = false;
    for (const auto& act : acts) {
      if (act.pc_symm == &pc_symm) {
        have_actions = true;
        break;
      }
    }
    if (!have_actions)
      return true;
  }

  out << "\n  puppet:";

  bool good = true;
  if (!maybe_espresso.empty()) {
    good = oput_protocon_pc_acts_espresso(out, pc_symm, acts, maybe_espresso);
  }
  else {
    for (const auto& act : acts) {
      if (act.pc_symm == &pc_symm) {
        oput_protocon_pc_act (out, act);
      }
    }
  }

  out << "\n    ;";
  return good;
}

static
  bool
oput_protocon_pc_assume (std::ostream& out, const Xn::PcSymm& pc_symm)
{
  const auto& assume_expression = pc_symm.spec->closed_assume_expression;
  if (assume_expression.empty())
    return true;
  out << "\n  (assume & closed)\n    (" << assume_expression << ");";
  return true;
}

static
  std::string
string_of_invariant_style (Xn::InvariantStyle style, Xn::InvariantScope scope)
{
  std::ostringstream oss;
  const char* pfx = "";
  const char* sfx = "";

  switch (scope)
  {
    case Xn::DirectInvariant:
      break;
    case Xn::ShadowInvariant:
      oss << "(";
      sfx = " % puppet)";
      break;
    case Xn::FutureInvariant:
      pfx = "future ";
      break;
    case Xn::NInvariantScopes:
      Claim( 0 );
  }

  oss << "(future & " << pfx;
  switch (style)
  {
    case Xn::FutureAndClosed:
      oss << "closed";
      break;
    case Xn::FutureAndSilent:
      oss << "silent";
      break;
    case Xn::FutureAndShadow:
      oss << "shadow";
      break;
    case Xn::FutureAndActiveShadow:
      oss << "active shadow";
      break;
    case Xn::NInvariantStyles:
      Claim( 0 );
  }
  oss << ")" << sfx;
  return oss.str();
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
oput_protocon_pc_invariant(std::ostream& out, const Xn::PcSymm& pc_symm,
                           const std::string_view style_str)
{
  const auto& invariant_expression = pc_symm.spec->invariant_expression;
  if (invariant_expression.empty())
    return true;

  out << "\n  " << style_str
    << "\n    (" << invariant_expression << ");";
  return true;
}

  bool
oput_protocon_file(std::ostream& out, const Xn::Sys& sys,
                   const Xn::Net& o_topology,
                   const std::vector<Action_id>& actions,
                   std::string_view maybe_espresso,
                   std::string_view comment)
{
  DeclLegit( good );

  const Xn::Net& topo = sys.topology;
  if (!comment.empty()) {
    out << "// " << comment;
  }
  oput_protocon_constants(out, *o_topology.spec);
  for (uint i = 0; i < topo.vbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = topo.vbl_symms[i];
    out << '\n';
    if (vbl_symm.pure_shadow_ck())
      out << "shadow ";
    else if (vbl_symm.pure_puppet_ck())
      out << "puppet ";

    out << "variable " << vbl_symm.spec->name
      << "[" << vbl_symm.spec->nmembs_expression
      << "] < " << vbl_symm.spec->domsz_expression << ";";
  }

  for (uint i = 0; i < sys.predicate_map.sz(); ++i) {
    out << "\npredicate " << sys.predicate_map.keys[i]
      << " :=\n  " << sys.predicate_map.expressions[i] << ";";
  }

  if (!sys.spec->closed_assume_expression.empty()) {
    out << "\n(assume & closed)\n  (" << sys.spec->closed_assume_expression << ")\n  ;";
  }

  std::string style_str =
    string_of_invariant_style (sys.spec->invariant_style,
                               sys.spec->invariant_scope);
  if (!sys.spec->invariant_expression.empty()) {
    const auto& legit_str = sys.spec->invariant_expression;
    out << "\n" << style_str << "\n  (" << legit_str << ")\n  ;";
  }

  if (sys.spec->invariant_behav != Xn::FutureShadow &&
      sys.spec->invariant_behav != Xn::NInvariantBehavs) {
    out << "\n" << string_of_invariant_behav (sys.spec->invariant_behav) << ";";
  }


  std::vector<Xn::ActSymm> acts;
  for (auto act_id : actions) {
    for (const auto& a : topo.represented_actions[act_id]) {
      sys.topology.action(acts.emplace_back(), a);
    }
  }
  std::sort(acts.begin(), acts.end());

  for (uint i = 0; i < sys.topology.pc_symms.sz(); ++i) {
    const Xn::PcSymm& pc_symm = sys.topology.pc_symms[i];
    if (pc_symm.membs.sz() == 0)  continue;

    out << "\nprocess " << pc_symm.spec->name
      << "[" << pc_symm.spec->idx_name
      ;
    if (!pc_symm.spec->idxmap_name.empty()) {
      out << " <- map " << pc_symm.spec->idxmap_name
        << " < " << o_topology.pc_symms[i].spec->nmembs_expression
        << " : " << pc_symm.spec->idxmap_expression;
    }
    else {
      out << " < " << o_topology.pc_symms[i].spec->nmembs_expression;
    }
    out << "]" << "\n{";
    oput_protocon_pc_lets(out, pc_symm);
    oput_protocon_pc_vbls(out, pc_symm);
    oput_protocon_pc_predicates(out, pc_symm);
    DoLegitLine("output assume")
      oput_protocon_pc_assume(out, pc_symm);
    DoLegitLine("output invariant")
      oput_protocon_pc_invariant(out, pc_symm, style_str);
    DoLegitLine("output actions")
      oput_protocon_pc_acts(out, pc_symm, acts, maybe_espresso);
    out << "\n}\n";
  }

  return good;
}

  bool
oput_protocon_file(
    std::ostream& out, const Xn::Sys& sys,
    const std::vector<Action_id>& actions,
    std::string_view maybe_espresso, std::string_view comment)
{
  return oput_protocon_file(out, sys, sys.topology, actions, maybe_espresso, comment);
}

  bool
oput_protocon_file(std::ostream& out, const Xn::Sys& sys,
                   std::string_view maybe_espresso, std::string_view comment)
{
  return oput_protocon_file(out, sys, sys.actions, maybe_espresso, comment);
}

  bool
oput_protocon_file(
    const std::string& ofilename,
    const Xn::Sys& sys,
    const Xn::Net& o_topology,
    const std::vector<Action_id>& actions,
    std::string_view maybe_espresso,
    std::string_view comment)
{
  fildesh::ofstream out(ofilename.c_str());
  if (!out.good()) {return false;}
  return oput_protocon_file(out, sys, o_topology, actions, maybe_espresso, comment);
}

  bool
oput_protocon_file(
    const std::string& ofilename,
    const Xn::Sys& sys,
    std::string_view maybe_espresso,
    std::string_view comment)
{
  return oput_protocon_file(
      ofilename, sys, sys.topology, sys.actions, maybe_espresso, comment);
}

END_NAMESPACE

