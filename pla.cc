
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

  of << ".mv " << (pc_symm.rvbl_symms.sz() + pc_symm.wmap.sz()) << " 0";
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i)
    of << ' ' << pc_symm.doms[i];
  for (uint i = 0; i < pc_symm.wmap.sz(); ++i)
    of << ' ' << pc_symm.doms[pc_symm.wmap[i]];
  of << '\n';

  of << '#';
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i)
    of << ' ' << pc_symm.vbl_name(i);

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

  void
oput_protocon_pc_vbls (Cx::OFile& of, const Xn::PcSymm& pc_symm, const Cx::String& idxname)
{
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    of << "  " << (pc_symm.write_flags[i] ? "write" : "read") << ": ";
    of << pc_symm.vbl_name(i, idxname);
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
  of << "  puppet action:\n    ( ";
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
  of << " );\n";
  return good;
}

  bool
oput_protocon_pc_acts (Cx::OFile& of, const Xn::PcSymm& pc_symm,
                       const Cx::String& idxname,
                       const Cx::Table<Xn::ActSymm>& acts,
                       OSPc* ospc)
{
  Sign good = 1;

  // Names for variables.
  Cx::Table<Cx::String> guard_vbls( pc_symm.rvbl_symms.sz() );
  Cx::Table<Cx::String> assign_vbls( pc_symm.wmap.sz() );
  for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
    guard_vbls[i] = pc_symm.vbl_name(i, idxname);
  }
  for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
    assign_vbls[i] = pc_symm.vbl_name(pc_symm.wmap[i], idxname);
  }

  DoLegit(good, "spawn process")
    good = spawn_OSPc (ospc);

  if (good)
  {
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
      oput_protocon_pc_act (of, olay, guard_vbls, assign_vbls);
  }

  close_OSPc (ospc);
  return good;
}

  bool
oput_protocon_file (Cx::OFile& of, const Xn::Sys& sys)
{
  Sign good = 1;
  OSPc ospc[1];
  *ospc = dflt_OSPc ();

  stdxpipe_OSPc (ospc);
  stdopipe_OSPc (ospc);
  ospc->cmd = cons1_AlphaTab ("espresso");

  const Cx::String idxname( "i" );

  const Xn::Net& topo = sys.topology;
  for (uint i = 0; i < topo.vbl_symms.sz(); ++i) {
    const Xn::VblSymm& vbl_symm = topo.vbl_symms[i];
    if (vbl_symm.shadow_puppet_role == Xn::Vbl::Shadow)
      of << "shadow\n";
    if (vbl_symm.shadow_puppet_role == Xn::Vbl::Puppet)
      of << "puppet\n";

    of << "variable " << vbl_symm.name
      << "[Nat % " << vbl_symm.membs.sz()
      << "] <- Nat % " << vbl_symm.domsz << ";\n";
  }

  Cx::Table<Xn::ActSymm> acts( sys.actions.size() );
  for (uint i = 0; i < sys.actions.size(); ++i) {
    topo.action(acts[i], sys.actions[i]);
  }

  for (uint i = 0; i < topo.pc_symms.sz(); ++i) {
    const Xn::PcSymm& pc_symm = topo.pc_symms[i];
    of << "process " << pc_symm.name
      << "[" << idxname << " <- Nat % " << pc_symm.membs.sz() << "]\n";
    of << "{\n";
    oput_protocon_pc_vbls (of, pc_symm, idxname);
    DoLegit(good, "output actions")
      good = oput_protocon_pc_acts (of, pc_symm, idxname, acts, ospc);
    of << "}\n";
  }

  if (sys.direct_invariant_ck())
    of << "direct";
  else
    of << "shadow";

  of << " invariant:\n  " << sys.invariant_expression << "\n  ;\n";

  lose_OSPc (ospc);
  return good;
}

