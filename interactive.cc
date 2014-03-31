
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

  enum PredicateInfluence { WithinPredicate, DisplayPredicate, NotInPredicate, IgnorePredicate };

  PredicateInfluence invariant_influence;
  PredicateInfluence silent_influence;
  PredicateInfluence cycle_influence;

  bool conj_invariant;
  bool conj_deadlock;
  bool conj_scc;
  Cx::PFmla* invariant_pfmla;
  Cx::PFmla* silent_pfmla;
  Cx::PFmla* cycle_pfmla;

  Interactive(const Xn::Sys& system)
    : sys(system)
    , topo(sys.topology)
    , invariant_influence(IgnorePredicate)
    , silent_influence(IgnorePredicate)
    , cycle_influence(IgnorePredicate)
    , invariant_pfmla(0)
    , silent_pfmla(0)
    , cycle_pfmla(0)
  {}

  ~Interactive()
  {
    delete invariant_pfmla;
    delete silent_pfmla;
    delete cycle_pfmla;
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
  if (invariant_influence != IgnorePredicate) {
    if (!invariant_pfmla) {
      invariant_pfmla = new Cx::PFmla(sys.invariant);
    }
    if (invariant_influence == WithinPredicate) {
      mask_pfmla &= *invariant_pfmla;
    }
    else if (invariant_influence == NotInPredicate) {
      mask_pfmla &= ~*invariant_pfmla;
    }
  }
  if (silent_influence != IgnorePredicate) {
    if (!silent_pfmla) {
      silent_pfmla = new Cx::PFmla(~xn.pre());
    }
    if (silent_influence == WithinPredicate) {
      mask_pfmla &= *silent_pfmla;
    }
    else if (silent_influence == NotInPredicate) {
      mask_pfmla &= ~*silent_pfmla;
    }
  }
  if (cycle_influence != IgnorePredicate) {
    if (!cycle_pfmla) {
      cycle_pfmla = new Cx::PFmla(false);
      xn.cycle_ck(cycle_pfmla);
    }
    if (cycle_influence == WithinPredicate) {
      mask_pfmla &= *cycle_pfmla;
    }
    else if (cycle_influence == NotInPredicate) {
      mask_pfmla &= ~*cycle_pfmla;
    }
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
      if (usim.invariant_influence != usim.IgnorePredicate) {
        of << "invariant "
          << (usim.invariant_pfmla->overlap_ck(pf) ? 1 : 0)
          << '\n';
      }
      if (usim.silent_influence != usim.IgnorePredicate) {
        of << "silent "
          << (usim.silent_pfmla->overlap_ck(pf) ? 1 : 0)
          << '\n';
      }
      if (usim.cycle_influence != usim.IgnorePredicate) {
        of << "cycle "
          << (usim.cycle_pfmla->overlap_ck(pf) ? 1 : 0)
          << '\n';
      }
      of << of.endl();
    }
    else if (skip_cstr_XFile(line_xf, "step")) {
      uint n = 0;
      skipds_XFile(line_xf, 0);
      bool forward = true;
      if (skip_cstr_XFile(line_xf, "img")) {
        forward = true;
      }
      else if (skip_cstr_XFile(line_xf, "pre")) {
        forward = false;
      }
      if (!xget_uint_XFile(line_xf, &n)) {
        n = 1;
      }
      while (n > 0) {
        n -= 1;
        Cx::Table<Cx::String> lines;
        if (forward) {
          usim.img_options(lines);
        }
        else {
          usim.pre_options(lines);
        }
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
    else if (skip_cstr_XFile(line_xf, "predicate")) {
      char* predicate_name = nextok_XFile (line_xf, 0, 0);
      char* predicate_influence = nextok_XFile (line_xf, 0, 0);
      Interactive::PredicateInfluence influence = Interactive::IgnorePredicate;

      if (eq_cstr(predicate_influence, "display")) {
        influence = Interactive::DisplayPredicate;
      }
      else if (eq_cstr(predicate_influence, "ignore")) {
        influence = Interactive::IgnorePredicate;
      }
      else if (eq_cstr(predicate_influence, "true")) {
        influence = Interactive::WithinPredicate;
      }
      else if (eq_cstr(predicate_influence, "false")) {
        influence = Interactive::NotInPredicate;
      }

      if (eq_cstr(predicate_name, "invariant")) {
        usim.invariant_influence = influence;
      }
      if (eq_cstr(predicate_name, "silent")) {
        usim.silent_influence = influence;
      }
      if (eq_cstr(predicate_name, "cycle")) {
        usim.cycle_influence = influence;
      }
      usim.reset_mask_pfmla();
    }
    else if (skip_cstr_XFile(line_xf, "exit"))
    {
      break;
    }
  }
}

