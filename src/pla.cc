
#include "pla.hh"

#include <fildesh/ostream.hh>
extern "C" {
#include <fildesh/fildesh_compat_sh.h>
#include <fildesh/fildesh_compat_fd.h>
#include <fildesh/fildesh_compat_string.h>
}

#include "xnsys.hh"

#include "namespace.hh"

static
  void
oput_pla_val(std::ostream& out, unsigned j, unsigned n)
{
  for (unsigned i = 0; i < n; ++i) {
    out << (i == j ? 1 : 0);
  }
}

static
  void
oput_pla_act(std::ostream& out, const Xn::ActSymm& act)
{
  const Xn::PcSymm& pc_symm = *act.pc_symm;
  for (unsigned i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.rvbl_symms[i];
    if (vbl_symm.pure_shadow_ck())
      continue;
    out << ' ';
    oput_pla_val(out, act.guard(i), vbl_symm.domsz);
  }
  for (unsigned i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.wvbl_symms[i];
    out << ' ';
    oput_pla_val(out, act.assign(i), vbl_symm.domsz);
  }
}

  void
oput_pla_pc_acts(std::ostream& out, const Xn::PcSymm& pc_symm,
                 const std::vector<Xn::ActSymm>& acts)
{
  assert(pc_symm.wvbl_symms.sz() == pc_symm.spec->wmap.sz());

  unsigned nrvbls = 0;
  for (const Xn::VblSymm* vbl_symm : pc_symm.rvbl_symms) {
    if (!vbl_symm->pure_shadow_ck()) {
      nrvbls += 1;
    }
  }

  out << ".mv " << (nrvbls + pc_symm.spec->wmap.sz()) << " 0";
  for (const Xn::VblSymm* vbl_symm : pc_symm.rvbl_symms) {
    if (!vbl_symm->pure_shadow_ck()) {
      out << ' ' << vbl_symm->domsz;
    }
  }
  for (const Xn::VblSymm* vbl_symm : pc_symm.wvbl_symms) {
    out << ' ' << vbl_symm->domsz;
  }
  out << '\n';

  out << '#';
  for (unsigned i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (pc_symm.rvbl_symms[i]->pure_shadow_ck())
      continue;
    out << ' ' << pc_symm.vbl_name(i);
  }

  for (auto pc_rvbl_idx : pc_symm.spec->wmap) {
    out << ' ' << pc_symm.vbl_name(pc_rvbl_idx) << '\'';
  }
  out << '\n';

  for (const Xn::ActSymm& act : acts) {
    if (act.pc_symm == &pc_symm) {
      oput_pla_act (out, act);
      out << '\n';
    }
  }
  out << ".e\n";
}

  bool
oput_pla_file (std::ostream& ofile, const Xn::Sys& sys)
{
  std::vector<Xn::ActSymm> acts;
  const Xn::Net& topo = sys.topology;
  for (auto act_id : sys.actions) {
    for (const auto& a : topo.represented_actions[act_id]) {
      topo.action(acts.emplace_back(), a);
    }
  }
  std::sort(acts.begin(), acts.end());
  for (unsigned i = 0; i < topo.pc_symms.sz(); ++i) {
    const Xn::PcSymm& pc_symm = topo.pc_symms[i];
    const Xn::PcSymmSpec& pc_spec = *pc_symm.spec;
    ofile << "## Process " << pc_spec.name << "[" << pc_spec.idx_name << "]:\n";
    oput_pla_pc_acts(ofile, pc_symm, acts);
  }
  return true;
}

  bool
oput_pla_file(const std::string& ofilename, const Xn::Sys& sys)
{
  fildesh::ofstream out(ofilename.c_str());
  if (out.fail()) {
    fildesh_log_error("Failed to create PLA file.");
    return false;
  }
  return oput_pla_file(out, sys);
}


static
  bool
oput_protocon_pc_act(std::ostream& out, FildeshX* in,
                     const std::vector<std::string>& guard_vbls,
                     const std::vector<std::string>& assign_vbls)
{
  bool clause = false;
  out << "\n    ( ";
  for (unsigned i = 0;
       i < (guard_vbls.size() + assign_vbls.size());
       ++i)
  {
    skipchrs_FildeshX(in, fildesh_compat_string_blank_bytes);

    unsigned m = 0;
    std::vector<unsigned> vals;
    while (peek_char_FildeshX(in, '0') || peek_char_FildeshX(in, '1')) {
      assert(in->at[in->off] == '0' || in->at[in->off] == '1');
      if (in->at[in->off] == '1') {
        vals.push_back(m);
      }
      skip_bytestring_FildeshX(in, NULL, 1);
      ++ m;
    }

    if (i >= guard_vbls.size()) {
      if (i == guard_vbls.size()) {
        out << " -->";
      }
      assert(vals.size() == 1);
      out << ' ' << assign_vbls[i-guard_vbls.size()] << ":=" << vals[0] << ';';
      continue;
    }

    if (vals.size() == m)  continue;

    if (clause)
      out << " && ";
    clause = true;

    if (vals.size() == m-1 && m > 2) {
      for (unsigned j = 0; j < m; ++j) {
        if (std::find(vals.begin(), vals.end(), j) != vals.end()) {
          out << guard_vbls[i] << "!=" << j;
          break;
        }
      }
      continue;
    }

    if (vals.size() > 1)  out << "(";
    for (unsigned j = 0; j < vals.size(); ++j) {
      if (j > 0)  out << " || ";
      out << guard_vbls[i] << "==" << vals[j];
    }
    if (vals.size() > 1)  out << ")";
  }
  out << " )";
  return true;
}


static
  bool
oput_protocon_pc_acts_espresso_spawn(std::ostream& out, const Xn::PcSymm& pc_symm,
                                     const std::vector<Xn::ActSymm>& acts,
                                     const char* const* argv)
{
  int istat = 0;
  fildesh_fd_t to_espresso_fd = -1;
  fildesh_fd_t in_espresso_fd = -1;
  fildesh_fd_t out_espresso_fd = -1;
  fildesh_fd_t from_espresso_fd = -1;
  fildesh_compat_pid_t pid = -1;

  // Names for variables.
  std::vector<std::string> guard_vbls;
  std::vector<std::string> assign_vbls( pc_symm.spec->wmap.size() );
  for (unsigned i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (!pc_symm.rvbl_symms[i]->pure_shadow_ck()) {
      guard_vbls.emplace_back() = pc_symm.vbl_name(i);
    }
  }
  for (unsigned i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    assign_vbls[i] = pc_symm.vbl_name(pc_symm.spec->wmap[i]);
  }

  if (istat == 0) {
    istat = fildesh_compat_fd_pipe(&to_espresso_fd, &in_espresso_fd);
    if (istat != 0) {fildesh_log_error("Failed to create pipe for espresso.");}
  }
  if (istat == 0) {
    istat = fildesh_compat_fd_pipe(&out_espresso_fd, &from_espresso_fd);
    if (istat != 0) {fildesh_log_error("Failed to create pipe for espresso.");}
  }
  if (istat == 0) {
    pid = fildesh_compat_fd_spawnvp(
        in_espresso_fd, out_espresso_fd, 2, NULL, argv);
    if (pid < 0) {
      istat = -1;
      fildesh_log_error("Failed to spawn espresso.");
    }
  }
  if (istat == 0) {
    fildesh::ostream to_espresso(open_fd_FildeshO(to_espresso_fd));
    oput_pla_pc_acts(to_espresso, pc_symm, acts);
  }

  FildeshX* from_espresso = NULL;
  if (istat == 0) {
    from_espresso = open_fd_FildeshX(from_espresso_fd);
    while (!skipstr_FildeshX(from_espresso, ".p")) {
      if (!getline_FildeshX(from_espresso)) {
        fildesh_log_error("espresso output finished early");
        istat = -1;
        break;
      }
    }
  }

  int n = -1;
  if (istat == 0) {
    if (!parse_int_FildeshX(from_espresso, &n)) {
      fildesh_log_error("Cannot parse number of lines");
      istat = -1;
    }
    getline_FildeshX(from_espresso);
  }

  for (int i = 0; istat == 0 && i < n; ++i) {
    FildeshX slice = sliceline_FildeshX(from_espresso);
    oput_protocon_pc_act(out, &slice, guard_vbls, assign_vbls);
  }
  out << "\n    ;";

  close_FildeshX(from_espresso);
  fildesh_log_errorf("istat %d");
  return (istat == 0);
}

  bool
oput_protocon_pc_acts_espresso(std::ostream& out,
                               const Xn::PcSymm& pc_symm,
                               const std::vector<Xn::ActSymm>& acts,
                               const std::string& espresso_name)
{
  const char* const argv[] = {
#if 1
    espresso_name.c_str(),
    // Using -Dexact can take a long time.
    // "-Dexact",
#else
    // Use this to capture espresso input/output.
    "sh",
    "-c",
    "tee in.pla | espresso | tee out.pla",
#endif
    NULL,
  };

  return oput_protocon_pc_acts_espresso_spawn(out, pc_symm, acts, argv);
}

END_NAMESPACE

