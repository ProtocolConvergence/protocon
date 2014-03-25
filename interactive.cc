
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
  const Xn::Sys& sys;
  const Xn::Net& topo;
  Cx::PFmla xn;
  Cx::PFmla mask_pfmla;

  bool conj_invariant;
  bool conj_deadlock;
  bool conj_scc;
  Cx::PFmla* invariant_pfmla;
  Cx::PFmla* deadlock_pfmla;
  Cx::PFmla* scc_pfmla;

  Interactive(const Xn::Sys& system)
    : sys(system)
    , topo(sys.topology)
    , conj_invariant(false)
    , conj_deadlock(false)
    , conj_scc(false)
    , invariant_pfmla(0)
    , deadlock_pfmla(0)
    , scc_pfmla(0)
  {}

  ~Interactive()
  {
    delete invariant_pfmla;
    delete deadlock_pfmla;
    delete scc_pfmla;
  }

  void assign(XFile* line_xf);
  void next_options(Cx::Table<Cx::String>& ret_lines, bool fwd) const;
  void img_options(Cx::Table<Cx::String>& ret_lines) const;
  void pre_options(Cx::Table<Cx::String>& ret_lines) const;
  void reset_mask_pfmla();
  Cx::PFmla state_pfmla() const;
  void randomize_state();
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
Interactive::assign(XFile* line_xf)
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
Interactive::next_options(Cx::Table<Cx::String>& ret_lines, bool fwd) const
{
  Cx::PFmla pf( topo.pfmla_ctx.pfmla_of_state(&state[0], all_vbls) );
  Cx::Table<uint> img_state(state);
  Cx::PFmla next( fwd ? xn.img(pf) : xn.pre(pf) );
  next &= this->mask_pfmla;
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
Interactive::img_options(Cx::Table<Cx::String>& ret_lines) const
{
  next_options(ret_lines, true);
}
  void
Interactive::pre_options(Cx::Table<Cx::String>& ret_lines) const
{
  next_options(ret_lines, false);
}

  void
Interactive::reset_mask_pfmla()
{
  mask_pfmla = true;
  if (conj_invariant) {
    if (!invariant_pfmla) {
      invariant_pfmla = new Cx::PFmla(sys.invariant);
    }
    mask_pfmla &= *invariant_pfmla;
  }
  if (conj_deadlock) {
    if (!deadlock_pfmla) {
      deadlock_pfmla = new Cx::PFmla(~xn.pre());
    }
    mask_pfmla &= *deadlock_pfmla;
  }
  if (conj_scc) {
    if (!scc_pfmla) {
      scc_pfmla = new Cx::PFmla(false);
      xn.cycle_ck(scc_pfmla);
    }
    mask_pfmla &= *scc_pfmla;
  }
}

  Cx::PFmla
Interactive::state_pfmla() const
{
  Cx::PFmla pf( true );
  for (uint i = 0; i < this->state.sz(); ++i) {
    pf &= (topo.pfmla_vbl(i) == this->state[i]);
  }
  return pf;
}

  void
Interactive::randomize_state()
{
  Cx::PFmla pf( this->mask_pfmla );
  if (!pf.sat_ck())  return;
  Cx::Table<uint> idcs( topo.vbls.sz() );
  for (uint i = 0; i < idcs.sz(); ++i) {
    idcs[i] = i;
  }
  this->urandom.shuffle(&idcs[0], idcs.sz());
  for (uint i = 0; i < idcs.sz(); ++i) {
    const Xn::Vbl& vbl = topo.vbls[idcs[i]];
    const Cx::PFmlaVbl& pfmla_vbl = topo.pfmla_vbl(idcs[i]);
    Cx::Table<uint> vals;
    for (uint j = 0; j < vbl.symm->domsz; ++j) {
      if (pf.overlap_ck(pfmla_vbl == j)) {
        vals.push(j);
      }
    }
    uint val = vals[this->urandom.pick(vals.sz())];
    this->state[idcs[i]] = val;
    pf &= (pfmla_vbl == val);
  }
}

  void
interactive(const Xn::Sys& sys)
{
  Interactive usim(sys);
  const Xn::Net& topo = sys.topology;
  usim.xn = sys.direct_pfmla;
  usim.mask_pfmla = true;
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
      usim.assign(line_xf);
    }
    else if (skip_cstr_XFile(line_xf, "topo"))
    {
      for (uint pcidx = 0; pcidx < topo.pcs.sz(); ++pcidx) {
        const Xn::Pc& pc = topo.pcs[pcidx];
        of << name_of(pc) << " {";
        for (uint i = 0; i < pc.rvbls.sz(); ++i) {
          if (pc.symm->write_flags[i])
            of << " write: ";
          else
            of << " read: ";
          of << name_of(*pc.rvbls[i]) << ";";
        }
        of << " }" << of.endl();
      }
      of << of.endl();
    }
    else if (skip_cstr_XFile(line_xf, "show-img"))
    {
      Cx::Table<Cx::String> lines;
      usim.img_options(lines);
      //std::sort (lines.begin(), lines.end());
      for (uint i = 0; i < lines.sz(); ++i) {
        of << lines[i] << '\n';
      }
      of << of.endl();
    }
    else if (skip_cstr_XFile(line_xf, "show-pre"))
    {
      Cx::Table<Cx::String> lines;
      usim.pre_options(lines);
      //std::sort (lines.begin(), lines.end());
      for (uint i = 0; i < lines.sz(); ++i) {
        of << lines[i] << '\n';
      }
      of << of.endl();
    }
    else if (skip_cstr_XFile(line_xf, "show-sat"))
    {
      Cx::PFmla pf = usim.state_pfmla();
      if (usim.conj_invariant) {
        of << "invariant "
          << (usim.invariant_pfmla->overlap_ck(pf) ? 1 : 0)
          << '\n';
      }
      if (usim.conj_deadlock) {
        of << "deadlock "
          << (usim.deadlock_pfmla->overlap_ck(pf) ? 1 : 0)
          << '\n';
      }
      if (usim.conj_scc) {
        of << "scc "
          << (usim.scc_pfmla->overlap_ck(pf) ? 1 : 0)
          << '\n';
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
        usim.img_options(lines);
        if (lines.sz()==0)
          break;
        Cx::String line = lines[usim.urandom.pick(lines.sz())];
        of << line << of.endl();
        init_XFile_olay_cstr(line_xf, line.cstr());
        usim.assign(line_xf);
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
    else if (skip_cstr_XFile(line_xf, "show-all-xn"))
    {
      topo.oput_all_xn(of, usim.xn);
      of << of.endl();
    }
    else if (skip_cstr_XFile(line_xf, "randomize")) {
      usim.randomize_state();
    }
    else if (skip_cstr_XFile(line_xf, "conj-invariant")) {
      uint flag = 0;
      if (!xget_uint_XFile(line_xf, &flag)) {
        flag = 1;
      }
      usim.conj_invariant = (flag == 1) ? true : false;
      usim.reset_mask_pfmla();
    }
    else if (skip_cstr_XFile(line_xf, "conj-deadlock")) {
      uint flag = 0;
      if (!xget_uint_XFile(line_xf, &flag)) {
        flag = 1;
      }
      usim.conj_deadlock = (flag == 1) ? true : false;
      usim.reset_mask_pfmla();
    }
    else if (skip_cstr_XFile(line_xf, "conj-scc")) {
      uint flag = 0;
      if (!xget_uint_XFile(line_xf, &flag)) {
        flag = 1;
      }
      usim.conj_scc = (flag == 1) ? true : false;
      usim.reset_mask_pfmla();
    }
    else if (skip_cstr_XFile(line_xf, "exit"))
    {
      break;
    }
  }
}

