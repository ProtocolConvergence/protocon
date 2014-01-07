
#include "interactive.hh"
#include "cx/ofile.hh"
#include "cx/xfile.hh"
#include "xnsys.hh"
#include "cx/urandom.hh"
#include <algorithm>

class Interactive
{
public:
  Cx::URandom urandom;
  Cx::Table<uint> all_vbls;
  Cx::Table<uint> state;
  Cx::PFmla xn;

  void assign(const Xn::Net& topo, XFile* line_xf);
  void next_options(Cx::Table<Cx::String>& ret_lines, const Xn::Sys& sys, bool fwd) const;
  void img_options(Cx::Table<Cx::String>& ret_lines, const Xn::Sys& sys) const;
  void pre_options(Cx::Table<Cx::String>& ret_lines, const Xn::Sys& sys) const;
};

static
  const Xn::Vbl*
parse_variable(XFile* xf, const Xn::Net& topo)
{
  static const char other_delims[] = ":=";
  char delims[sizeof(other_delims) - 1 + sizeof(WhiteSpaceChars)];

  {
    const uint sz = sizeof(other_delims)-1;
    memcpy(delims, other_delims, sz);
    memcpy(&delims[sz], WhiteSpaceChars, sizeof(WhiteSpaceChars));
  }
  skipds_XFile(xf, delims);
  for (uint i = 0; i < topo.vbls.sz(); ++i) {
    if (skip_cstr_XFile(xf, name_of(topo.vbls[i]).cstr())) {
      return &topo.vbls[i];
    }
  }
  return 0;
}

  void
Interactive::assign(const Xn::Net& topo, XFile* line_xf)
{
  for (const Xn::Vbl* vbl = parse_variable(line_xf, topo);
       vbl;
       vbl = parse_variable(line_xf, topo))
  {
    skipds_XFile(line_xf, WhiteSpaceChars);
    skip_cstr_XFile(line_xf, ":=");
    skip_cstr_XFile(line_xf, "=");
    int val = 0;
    if (xget_int_XFile(line_xf, &val)) {
      uint idx = topo.vbls.index_of(vbl);
      state[idx] = umod_int (val, vbl->symm->domsz);
      skipds_XFile(line_xf, WhiteSpaceChars);
      skip_cstr_XFile(line_xf, ";");
    }
  }
}

  void
Interactive::next_options(Cx::Table<Cx::String>& ret_lines, const Xn::Sys& sys, bool fwd) const
{
  const Xn::Net& topo = sys.topology;
  Cx::PFmla pf( topo.pfmla_ctx.pfmla_of_state(&state[0], all_vbls) );
  Cx::Table<uint> img_state(state);
  Cx::PFmla next( fwd ? xn.img(pf) : xn.pre(pf) );
  ret_lines.clear();
  for (uint vbl_idx = 0; vbl_idx < topo.vbls.sz(); ++vbl_idx) {
    Cx::PFmla local_pf( next & (topo.pfmla_vbl(vbl_idx) != state[vbl_idx]) );
    while (local_pf.sat_ck()) {
      local_pf.state(&img_state[0], all_vbls);
      const char* delim = "";
      Cx::String line;
      for (uint i = 0; i < img_state.sz(); ++i) {
        if (img_state[i] != state[i]) {
          line << delim << name_of(topo.vbls[i]) << ":=" << img_state[i] << ";";
          delim = " ";
        }
      }
      ret_lines.push(line);
      local_pf -= topo.pfmla_ctx.pfmla_of_state(&img_state[0], all_vbls);
    }
    next -= topo.pfmla_vbl(vbl_idx) != state[vbl_idx];
  }
}

  void
Interactive::img_options(Cx::Table<Cx::String>& ret_lines, const Xn::Sys& sys) const
{
  next_options(ret_lines, sys, true);
}
  void
Interactive::pre_options(Cx::Table<Cx::String>& ret_lines, const Xn::Sys& sys) const
{
  next_options(ret_lines, sys, false);
}

  void
interactive(const Xn::Sys& sys)
{
  Interactive usim;
  const Xn::Net& topo = sys.topology;
  usim.xn = sys.direct_pfmla;
  usim.all_vbls.grow(topo.vbls.sz(), 0);
  usim.state.grow(topo.vbls.sz(), 0);
  for (uint i = 0; i < topo.vbls.sz(); ++i) {
    usim.all_vbls[i] = topo.vbls[i].pfmla_idx;
  }

  Cx::OFile of( stdout_OFile() );
  XFile* xf = stdin_XFile();
  XFile line_xf[1];

  while (getlined_olay_XFile (line_xf, xf, "\n"))
  {
    skipds_XFile(line_xf, WhiteSpaceChars);
    if (skip_cstr_XFile(line_xf, "assign ") ||
        skip_cstr_XFile(line_xf, "a "))
    {
      usim.assign(topo, line_xf);
    }
    else if (skip_cstr_XFile(line_xf, "show-img"))
    {
      Cx::Table<Cx::String> lines;
      usim.img_options(lines, sys);
      //std::sort (lines.begin(), lines.end());
      for (uint i = 0; i < lines.sz(); ++i) {
        of << lines[i] << "\n";
      }
      of << of.endl();
    }
    else if (skip_cstr_XFile(line_xf, "show-pre"))
    {
      Cx::Table<Cx::String> lines;
      usim.pre_options(lines, sys);
      //std::sort (lines.begin(), lines.end());
      for (uint i = 0; i < lines.sz(); ++i) {
        of << lines[i] << "\n";
      }
      of << of.endl();
    }
    else if (skip_cstr_XFile(line_xf, "step")) {
      uint n = 0;
      if (!xget_uint_XFile(line_xf, &n)) {
        n = 1;
      }
      while (n > 0) {
        n -= 1;
        Cx::Table<Cx::String> lines;
        usim.img_options(lines, sys);
        if (lines.sz()==0)
          break;
        Cx::String line = lines[usim.urandom.pick(lines.sz())];
        of << line << of.endl();
        init_XFile_olay_cstr(line_xf, line.cstr());
        usim.assign(topo, line_xf);
      }
      of << of.endl();
    }
    else if (skip_cstr_XFile(line_xf, "show-state"))
    {
      for (uint i = 0; i < topo.vbls.sz(); ++i) {
        of << name_of(topo.vbls[i]) << "==" << usim.state[i] << '\n';
      }
      of << of.endl();
    }
    else if (skip_cstr_XFile(line_xf, "randomize")) {
      for (uint i = 0; i < topo.vbls.sz(); ++i) {
        usim.state[i] = usim.urandom.pick(topo.vbls[i].symm->domsz);
      }
    }
    else if (skip_cstr_XFile(line_xf, "exit"))
    {
      break;
    }
  }
}
