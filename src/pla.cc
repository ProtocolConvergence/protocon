
#include "pla.hh"

extern "C" {
#include "cx/ospc.h"
}
#include "lace_wrapped.hh"

#include "cx/alphatab.hh"
#include "cx/fileb.hh"
#include "cx/table.hh"
#include "xnsys.hh"

#include "namespace.hh"

static
  void
oput_pla_val(std::ostream& out, uint j, uint n)
{
  for (uint i = 0; i < n; ++i)
    out << (i == j ? 1 : 0);
}

static
  void
oput_pla_act(std::ostream& out, const Xn::ActSymm& act)
{
  const Xn::PcSymm& pc_symm = *act.pc_symm;
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.rvbl_symms[i];
    if (vbl_symm.pure_shadow_ck())
      continue;
    out << ' ';
    oput_pla_val(out, act.guard(i), vbl_symm.domsz);
  }
  for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.wvbl_symms[i];
    out << ' ';
    oput_pla_val(out, act.assign(i), vbl_symm.domsz);
  }
}

  void
oput_pla_pc_acts(std::ostream& out, const Xn::PcSymm& pc_symm,
                 const Table<Xn::ActSymm>& acts)
{
  Claim2( pc_symm.wvbl_symms.sz() ,==, pc_symm.spec->wmap.sz() );

  uint nrvbls = 0;
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (!pc_symm.rvbl_symms[i]->pure_shadow_ck())
      nrvbls += 1;
  }

  out << ".mv " << (nrvbls + pc_symm.spec->wmap.sz()) << " 0";
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.rvbl_symms[i];
    if (vbl_symm.pure_shadow_ck())
      continue;
    out << ' ' << vbl_symm.domsz;
  }
  for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.wvbl_symms[i];
    out << ' ' << vbl_symm.domsz;
  }
  out << '\n';

  out << '#';
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (pc_symm.rvbl_symms[i]->pure_shadow_ck())
      continue;
    out << ' ' << pc_symm.vbl_name(i);
  }

  for (uint i = 0; i < pc_symm.spec->wmap.sz(); ++i)
    out << ' ' << pc_symm.vbl_name(pc_symm.spec->wmap[i]) << '\'';
  out << '\n';

  for (uint i = 0; i < acts.sz(); ++i) {
    const Xn::ActSymm& act = acts[i];
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
  Table<Xn::ActSymm> acts;
  const Xn::Net& topo = sys.topology;
  for (uint i = 0; i < sys.actions.size(); ++i) {
    for (uint j = 0; j < topo.represented_actions[sys.actions[i]].sz(); ++j) {
      topo.action(acts.grow1(), topo.represented_actions[sys.actions[i]][j]);
    }
  }
  std::sort(acts.begin(), acts.end());
  for (uint i = 0; i < topo.pc_symms.sz(); ++i) {
    const Xn::PcSymm& pc_symm = topo.pc_symms[i];
    const Xn::PcSymmSpec& pc_spec = *pc_symm.spec;
    ofile << "## Process " << pc_spec.name << "[" << pc_spec.idx_name << "]:\n";
    oput_pla_pc_acts(ofile, pc_symm, acts);
  }
  return true;
}

  bool
oput_pla_file(const String& ofilename, const Xn::Sys& sys)
{
  DeclLegit( good );
  lace::ofstream out(ofilename.ccstr());
  DoLegitLine( "Open PLA file" )
    out.good();
  DoLegitLine( "" )
    oput_pla_file(out, sys);
  return good;
}


static
  bool
oput_protocon_pc_act(std::ostream& out, ::XFile* xf,
                     const Table<String>& guard_vbls,
                     const Table<String>& assign_vbls)
{
  DeclLegit( good );
  bool clause = false;
  out << "\n    ( ";
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
        out << " -->";
      }
      Claim2( vals.sz() ,==, 1 );
      out << ' ' << assign_vbls[i-guard_vbls.sz()] << ":=" << vals[0] << ';';
      continue;
    }

    if (vals.sz() == m)  continue;

    if (clause)
      out << " && ";
    clause = true;

    if (vals.sz() == m-1 && m > 2) {
      for (uint j = 0; j < m; ++j) {
        if (!vals.elem_ck(j)) {
          out << guard_vbls[i] << "!=" << j;
          break;
        }
      }
      continue;
    }

    if (vals.sz() > 1)  out << "(";
    for (uint j = 0; good && j < vals.sz(); ++j) {
      if (j > 0)  out << " || ";
      out << guard_vbls[i] << "==" << vals[j];
    }
    if (vals.sz() > 1)  out << ")";
  }
  out << " )";
  return good;
}


static
  bool
oput_protocon_pc_acts_espresso_spawn(std::ostream& out, const Xn::PcSymm& pc_symm,
                                     const Table<Xn::ActSymm>& acts,
                                     OSPc* ospc)
{
  DeclLegit( good );

  // Names for variables.
  Table<String> guard_vbls;
  Table<String> assign_vbls( pc_symm.spec->wmap.sz() );
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (pc_symm.rvbl_symms[i]->pure_shadow_ck())
      continue;
    guard_vbls.push(pc_symm.vbl_name(i));
  }
  for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    assign_vbls[i] = pc_symm.vbl_name(pc_symm.spec->wmap[i]);
  }

  DoLegitLine( "spawn espresso" )
    spawn_OSPc(ospc);

  if (good) {
    lace::ofstream to_espresso(open_fd_LaceO(ospc->ofb.fb.fd));
    oput_pla_pc_acts(to_espresso, pc_symm, acts);
  }
  if (good) {
    /* Double-close is unavoidable unless we dup() above.*/
    fclose(ospc->ofb.fb.f);
    ospc->ofb.fb.f = NULL;
    ospc->ofb.fb.fd = -1;
  }

  while (good && !skip_cstr_XFile (ospc->xf, ".p"))
  {
    DoLegitLine("get line")
      !!getline_XFile (ospc->xf);
  }

  uint n = 0;
  DoLegitLine("read number of lines from espresso")
    xget_uint_XFile (ospc->xf, &n);

  getline_XFile (ospc->xf);

  for (uint i = 0; good && i < n; ++i) {
    ::XFile olay[1];

    DoLegitLine("get line from espresso")
      getlined_olay_XFile (olay, ospc->xf, "\n");

    DoLegitLine(0)
      oput_protocon_pc_act(out, olay, guard_vbls, assign_vbls);
  }
  out << "\n    ;";

  close_OSPc (ospc);
  return good;
}

  bool
oput_protocon_pc_acts_espresso(std::ostream& out,
                               const Xn::PcSymm& pc_symm,
                               const Table<Xn::ActSymm>& acts)
{
  DeclLegit( good );
  OSPc ospc[1];
  *ospc = dflt_OSPc ();

  stdxpipe_OSPc (ospc);
  stdopipe_OSPc (ospc);
  ospc->cmd = cons1_AlphaTab ("espresso");
  /* Using -Dexact can take a long time.*/
  //PushTable( ospc->args, cons1_AlphaTab ("-Dexact") );

  if (false) {
    // Use this to capture espresso input/output.
    ospc->cmd = cons1_AlphaTab ("sh");
    PushTable( ospc->args, cons1_AlphaTab ("-c") );
    PushTable( ospc->args, cons1_AlphaTab ("tee in.pla | espresso | tee out.pla") );
  }

  DoLegitLine( "" )
    oput_protocon_pc_acts_espresso_spawn(out, pc_symm, acts, ospc);

  lose_OSPc (ospc);
  return good;
}

END_NAMESPACE

