
#include "interactive.hh"
#include "lace_wrapped.hh"
#include "xnsys.hh"
#include "cx/urandom.hh"
#include <algorithm>

extern "C" {
#include "fildesh_compat_string.h"
}

#include "namespace.hh"

class Interactive
{
public:
  URandom urandom;
  Table<uint> all_vbls;
  Table<uint> state;
  const Xn::Sys& sys;
  const Xn::Net& topo;
  X::Fmla xn;
  P::Fmla mask_pfmla;

  enum PredicateInfluence { WithinPredicate, DisplayPredicate, NotInPredicate, IgnorePredicate };

  PredicateInfluence invariant_influence;
  PredicateInfluence silent_influence;
  PredicateInfluence cycle_influence;

  bool conj_invariant;
  bool conj_deadlock;
  bool conj_scc;
  P::Fmla* invariant_pfmla;
  P::Fmla* silent_pfmla;
  P::Fmla* cycle_pfmla;

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

  void assign(FildeshX* in);
  void next_options(Table<String>& ret_lines, bool fwd) const;
  void img_options(Table<String>& ret_lines) const;
  void pre_options(Table<String>& ret_lines) const;
  void reset_mask_pfmla();
  P::Fmla state_pfmla() const;
  void randomize_state();
};

static
  const Xn::Vbl*
parse_variable(FildeshX* in, const Xn::Net& topo)
{
  static const char other_delims[] = ":=";
  char delims[sizeof(other_delims) - 1 + sizeof(fildesh_compat_string_blank_bytes)];

  {
    const uint sz = sizeof(other_delims)-1;
    memcpy(delims, other_delims, sz);
    memcpy(&delims[sz], fildesh_compat_string_blank_bytes, sizeof(fildesh_compat_string_blank_bytes));
  }
  skipchrs_FildeshX(in, delims);
  for (uint i = 0; i < topo.vbls.sz(); ++i) {
    if (skipstr_FildeshX(in, name_of(topo.vbls[i]).cstr())) {
      return &topo.vbls[i];
    }
  }
  return NULL;
}

  void
Interactive::assign(FildeshX* in)
{
  for (const Xn::Vbl* vbl = parse_variable(in, topo);
       vbl;
       vbl = parse_variable(in, topo))
  {
    skipchrs_FildeshX(in, fildesh_compat_string_blank_bytes);
    skipchrs_FildeshX(in, ":");
    skipchrs_FildeshX(in, "=");
    int val = 0;
    if (parse_int_FildeshX(in, &val)) {
      uint idx = topo.vbls.index_of(vbl);
      state[idx] = umod_int (val, vbl->symm->domsz);
      skipchrs_FildeshX(in, fildesh_compat_string_blank_bytes);
      skipchrs_FildeshX(in, ";");
    }
  }
}

  void
Interactive::next_options(Table<String>& ret_lines, bool fwd) const
{
  P::Fmla pf( topo.pfmla_ctx.pfmla_of_state(&state[0], all_vbls) );
  Table<uint> img_state(state);
  P::Fmla next( fwd ? xn.img(pf) : xn.pre(pf) );
  next &= this->mask_pfmla;
  ret_lines.clear();
  for (uint vbl_idx = 0; vbl_idx < topo.vbls.sz(); ++vbl_idx) {
    P::Fmla local_pf( next & (topo.pfmla_vbl(vbl_idx) != state[vbl_idx]) );
    while (local_pf.sat_ck()) {
      local_pf.state(&img_state[0], all_vbls);
      const char* delim = "";
      String line;
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
Interactive::img_options(Table<String>& ret_lines) const
{
  next_options(ret_lines, true);
}
  void
Interactive::pre_options(Table<String>& ret_lines) const
{
  next_options(ret_lines, false);
}

  void
Interactive::reset_mask_pfmla()
{
  mask_pfmla = sys.closed_assume;
  if (invariant_influence != IgnorePredicate) {
    if (!invariant_pfmla) {
      invariant_pfmla = new P::Fmla(sys.invariant);
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
      silent_pfmla = new P::Fmla(sys.closed_assume & ~xn.pre());
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
      cycle_pfmla = new P::Fmla(false);
      xn.cycle_ck(cycle_pfmla, sys.closed_assume);
    }
    if (cycle_influence == WithinPredicate) {
      mask_pfmla &= *cycle_pfmla;
    }
    else if (cycle_influence == NotInPredicate) {
      mask_pfmla &= ~*cycle_pfmla;
    }
  }
}

  P::Fmla
Interactive::state_pfmla() const
{
  P::Fmla pf( true );
  for (uint i = 0; i < this->state.sz(); ++i) {
    pf &= (topo.pfmla_vbl(i) == this->state[i]);
  }
  return pf;
}

  void
Interactive::randomize_state()
{
  P::Fmla pf( this->mask_pfmla );
  if (!pf.sat_ck())  return;
  Table<uint> idcs( topo.vbls.sz() );
  for (uint i = 0; i < idcs.sz(); ++i) {
    idcs[i] = i;
  }
  this->urandom.shuffle(&idcs[0], idcs.sz());
  for (uint i = 0; i < idcs.sz(); ++i) {
    const Xn::Vbl& vbl = topo.vbls[idcs[i]];
    const PFmlaVbl& pfmla_vbl = topo.pfmla_vbl(idcs[i]);
    Table<uint> vals;
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
  usim.mask_pfmla = sys.closed_assume;
  usim.all_vbls.grow(topo.vbls.sz(), 0);
  usim.state.grow(topo.vbls.sz(), 0);
  for (uint i = 0; i < topo.vbls.sz(); ++i) {
    usim.all_vbls[i] = topo.vbls[i].pfmla_idx;
  }

  lace::ofstream of("/dev/stdout");
  FildeshX* in = open_FildeshXF("/dev/stdin");
  if (!in) {
    fildesh_log_error("failed to open stdin");
    return;
  }

  for (FildeshX line_slice = sliceline_FildeshX(in);
       line_slice.at;
       line_slice = sliceline_FildeshX(in))
  {
    skipchrs_FildeshX(&line_slice, fildesh_compat_string_blank_bytes);

    if (skipstr_FildeshX(&line_slice, "assign") || skipstr_FildeshX(&line_slice, "a")) {
      usim.assign(&line_slice);
    }
    else if (skipstr_FildeshX(&line_slice, "topo")) {
      for (uint pcidx = 0; pcidx < topo.pcs.sz(); ++pcidx) {
        const Xn::Pc& pc = topo.pcs[pcidx];
        of << name_of(pc) << " {";
        for (uint i = 0; i < pc.rvbls.sz(); ++i) {
          if (pc.symm->spec->access[i].write_ck())
            of << " write: ";
          else
            of << " read: ";
          of << name_of(*pc.rvbls[i]) << ";";
        }
        of << " }" << std::endl;
      }
      of << std::endl;
    }
    else if (skipstr_FildeshX(&line_slice, "show-img")) {
      Table<String> lines;
      usim.img_options(lines);
      //std::sort (lines.begin(), lines.end());
      for (uint i = 0; i < lines.sz(); ++i) {
        of << lines[i] << '\n';
      }
      of << std::endl;
    }
    else if (skipstr_FildeshX(&line_slice, "show-pre")) {
      Table<String> lines;
      usim.pre_options(lines);
      //std::sort (lines.begin(), lines.end());
      for (uint i = 0; i < lines.sz(); ++i) {
        of << lines[i] << '\n';
      }
      of << std::endl;
    }
    else if (skipstr_FildeshX(&line_slice, "show-sat")) {
      P::Fmla pf = usim.state_pfmla();
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
      of << std::endl;
    }
    else if (skipstr_FildeshX(&line_slice, "step")) {
      skipchrs_FildeshX(&line_slice, fildesh_compat_string_blank_bytes);
      bool forward = true;
      if (skipstr_FildeshX(&line_slice, "img")) {
        forward = true;
      }
      else if (skipstr_FildeshX(&line_slice, "pre")) {
        forward = false;
      }
      unsigned n = 1; /* default */
      int x = -1;
      if (parse_int_FildeshX(&line_slice, &x) && x >= 0) {
        n = x;
      }
      while (n > 0) {
        n -= 1;
        Table<String> lines;
        if (forward) {
          usim.img_options(lines);
        }
        else {
          usim.pre_options(lines);
        }
        if (lines.sz()==0)
          break;
        String line = lines[usim.urandom.pick(lines.sz())];
        of << line << std::endl;
        line_slice.at = line.cstr();
        line_slice.off = 0;
        line_slice.size = strlen(line.cstr());
        usim.assign(&line_slice);
      }
      of << std::endl;
    }
    else if (skipstr_FildeshX(&line_slice, "sstep")) {
      skipchrs_FildeshX(&line_slice, fildesh_compat_string_blank_bytes);
      bool forward = true;
      unsigned n = 1; /* default */
      int x = -1;
      if (parse_int_FildeshX(&line_slice, &x) && x >= 0) {
        n = x;
      }
      while (n > 0) {
        n -= 1;
        Table<String> lines;
        if (forward) {
          usim.img_options(lines);
        }
        if (lines.sz()==0)
          break;
        for (uint i = 0; i < lines.sz(); ++i) {
          String line = lines[i];
          of << line << std::endl;
          line_slice.at = line.cstr();
          line_slice.off = 0;
          line_slice.size = strlen(line.cstr());
          usim.assign(&line_slice);
        }
      }
      of << std::endl;
    }
    else if (skipstr_FildeshX(&line_slice, "show-state"))
    {
      for (uint i = 0; i < topo.vbls.sz(); ++i) {
        of << name_of(topo.vbls[i]) << "==" << usim.state[i] << '\n';
      }
      of << std::endl;
    }
    else if (skipstr_FildeshX(&line_slice, "show-all-xn"))
    {
      topo.oput_all_xn(of, usim.xn);
      of << std::endl;
    }
    else if (skipstr_FildeshX(&line_slice, "randomize")) {
      usim.randomize_state();
    }
    else if (skipstr_FildeshX(&line_slice, "predicate")) {
      skipchrs_FildeshX(
          &line_slice, fildesh_compat_string_blank_bytes);
      FildeshX predicate_name = slicechrs_FildeshX(
          &line_slice, fildesh_compat_string_blank_bytes);

      skipchrs_FildeshX(
          &line_slice, fildesh_compat_string_blank_bytes);
      FildeshX predicate_influence = slicechrs_FildeshX(
          &line_slice, fildesh_compat_string_blank_bytes);

      Interactive::PredicateInfluence influence = Interactive::IgnorePredicate;
      if (eq_cstr(predicate_influence.at, "display")) {
        influence = Interactive::DisplayPredicate;
      }
      else if (eq_cstr(predicate_influence.at, "ignore")) {
        influence = Interactive::IgnorePredicate;
      }
      else if (eq_cstr(predicate_influence.at, "true")) {
        influence = Interactive::WithinPredicate;
      }
      else if (eq_cstr(predicate_influence.at, "false")) {
        influence = Interactive::NotInPredicate;
      } else {
        fildesh_log_warningf("Unknown predicate influence: %s", predicate_influence.at);
      }

      if (eq_cstr(predicate_name.at, "invariant")) {
        usim.invariant_influence = influence;
      }
      else if (eq_cstr(predicate_name.at, "silent")) {
        usim.silent_influence = influence;
      }
      else if (eq_cstr(predicate_name.at, "cycle")) {
        usim.cycle_influence = influence;
      }
      else {
        fildesh_log_warningf("Unknown predicate name: %s", predicate_name.at);
      }
      usim.reset_mask_pfmla();
    }
    else if (skipstr_FildeshX(&line_slice, "exit"))
    {
      break;
    }
  }
  close_FildeshX(in);
}

END_NAMESPACE

