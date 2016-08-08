
#include "pla.hh"

extern "C" {
#include "cx/ospc.h"
}

#include "cx/alphatab.hh"
#include "cx/fileb.hh"
#include "cx/table.hh"
#include "xnsys.hh"

#include "namespace.hh"

static
  void
oput_pla_val (OFile& of, uint j, uint n)
{
  for (uint i = 0; i < n; ++i)
    of << (i == j ? 1 : 0);
}

static
  void
oput_pla_act (OFile& of, const Xn::ActSymm& act)
{
  const Xn::PcSymm& pc_symm = *act.pc_symm;
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.rvbl_symms[i];
    if (vbl_symm.pure_shadow_ck())
      continue;
    of << ' ';
    oput_pla_val (of, act.guard(i), vbl_symm.domsz);
  }
  for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.wvbl_symms[i];
    of << ' ';
    oput_pla_val (of, act.assign(i), vbl_symm.domsz);
  }
}

  void
oput_pla_pc_acts (OFile& of, const Xn::PcSymm& pc_symm,
                  const Table<Xn::ActSymm>& acts)
{
  Claim2( pc_symm.wvbl_symms.sz() ,==, pc_symm.spec->wmap.sz() );

  uint nrvbls = 0;
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (!pc_symm.rvbl_symms[i]->pure_shadow_ck())
      nrvbls += 1;
  }

  of << ".mv " << (nrvbls + pc_symm.spec->wmap.sz()) << " 0";
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.rvbl_symms[i];
    if (vbl_symm.pure_shadow_ck())
      continue;
    of << ' ' << vbl_symm.domsz;
  }
  for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = *pc_symm.wvbl_symms[i];
    of << ' ' << vbl_symm.domsz;
  }
  of << '\n';

  of << '#';
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    if (pc_symm.rvbl_symms[i]->pure_shadow_ck())
      continue;
    of << ' ' << pc_symm.vbl_name(i);
  }

  for (uint i = 0; i < pc_symm.spec->wmap.sz(); ++i)
    of << ' ' << pc_symm.vbl_name(pc_symm.spec->wmap[i]) << '\'';
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

  bool
oput_pla_file (OFile& ofile, const Xn::Sys& sys)
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
    oput_pla_pc_acts (ofile, pc_symm, acts);
  }
  return true;
}

  bool
oput_pla_file (const String& ofilename, const Xn::Sys& sys)
{
  DeclLegit( good );
  Cx::OFileB ofb;
  OFile ofile = ofb.uopen(ofilename);
  DoLegitLine( "Open PLA file" )
    !!ofile;
  DoLegitLine( "" )
    oput_pla_file (ofile, sys);
  return good;
}


static
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


static
  bool
oput_protocon_pc_acts_espresso_spawn (OFile& of, const Xn::PcSymm& pc_symm,
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
    spawn_OSPc (ospc);

  if (good) {
    OFile espresso_xf(ospc->of);
    oput_pla_pc_acts (espresso_xf, pc_symm, acts);
    close_OFile (ospc->of);
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
      oput_protocon_pc_act (of, olay, guard_vbls, assign_vbls);
  }
  of << "\n    ;";

  close_OSPc (ospc);
  return good;
}

  bool
oput_protocon_pc_acts_espresso (OFile& of,
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
    oput_protocon_pc_acts_espresso_spawn (of, pc_symm, acts, ospc);

  lose_OSPc (ospc);
  return good;
}

END_NAMESPACE

