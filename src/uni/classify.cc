
#include <algorithm>

#include <fildesh/ostream.hh>

#include "livelock.hh"
#include "uniact.hh"
#include "unifile.hh"

#include "src/pfmla.hh"
#include "src/cx/bittable.hh"

#include "src/inline/eq_cstr.h"

#include "src/namespace.hh"


/** Given a list of actions and variables x[j-1] and x[j],
 * compute the tiling constraints for column j
 * in the form of a transition formula.
 **/
static
  X::Fmla
column_xfmla(const Table<UniAct>& acts, const PFmlaVbl& x_p, const PFmlaVbl& x_j)
{
  X::Fmla xn( false );
  for (uint i = 0; i < acts.sz(); ++i) {
    const UniAct& act = acts[i];
    //    x'[j-1]==a         && x[j]==b     && x'[j]==c
    xn |= x_p.img_eq(act[0]) && x_j==act[1] && x_j.img_eq(act[2]);
  }
  return xn;
}

static
  void
bdd_init_vbls(PFmlaCtx& pfmla_ctx, Table<PFmlaVbl>& vbls,
              uint max_period, uint domsz)
{
  vbls.affysz(1+max_period);
  for (unsigned i = 0; i < 1+max_period; ++i) {
    unsigned vbl_id = pfmla_ctx.add_vbl("x" + std::to_string(i), domsz);
    vbls[i] = pfmla_ctx.vbl(vbl_id);
  }
}

static
  uint
bdd_classify(const Table<PcState>& ppgfun,
             Table<PFmlaVbl>& vbls,
             uint min_period, uint max_period,
             const uint domsz)
{
  Table<UniAct> acts = uniring_actions_of(ppgfun, domsz);

  X::Fmla xn(true);
  for (uint j = 1; j < 1+max_period; ++j) {
    xn &= column_xfmla(acts, vbls[j-1], vbls[j]);
    skip_unless (j >= min_period);
    const X::Fmla periodic_xn =
      xn & (vbls[0]==vbls[j]) & (vbls[0].img_eq_img(vbls[j]));

    if (periodic_xn.cycle_ck(0)) {
      return j;
    }
  }

  // No livelocks found? Are they even a possibility?
  if (!xn.cycle_ck(0)) {
    return 0;
  }
  return max_period+1;
}

static
  uint
tile_classify(const Table<PcState>& ppgfun, uint max_period, const uint domsz)
{
  Table<PcState> row;
  const Trit exists =
    livelock_semick(max_period, ppgfun, domsz, &row);
  if (exists == Nil)  return 0;
  if (exists == Yes)  return row.sz()-1;
  return max_period + 1;
}

/** Execute me now!**/
int main(int argc, char** argv) {
  int argi = 1;

  uint min_period = 0;
  uint max_period = 0;
  uint domsz = 0;

  bool use_bdds = true;

  fildesh::ofstream silent_ofile;
  fildesh::ofstream livelock_ofile;
  fildesh::ofstream unknown_ofile;

  FildeshX* in = NULL;
  std::ostream& ofile = std::cout;

  bool line_flush = true;

  while (argi < argc) {
    const char* arg = argv[argi++];
    if (eq_cstr ("-id", arg)) {
      if (!argv[argi])
        failout_sysCx("Argument Usage: -id <id>");
      close_FildeshX(in);
      in = open_FildeshXA();
      size_t n = strlen(argv[argi]);
      memcpy(grow_FildeshX(in, n), argv[argi], n);
      argi += 1;
    }
    else if (eq_cstr ("-nobdd", arg)) {
      use_bdds = false;
    }
    else if (eq_cstr ("-cutoff", arg)) {
      // Ignored.
    }
    else if (eq_cstr ("-flushoff", arg)) {
      line_flush = false;
    }
    else if (eq_cstr ("-silent", arg) || eq_cstr ("-sil", arg)) {
      silent_ofile.open("/dev/stdout");
    }
    else if (eq_cstr ("-livelock", arg) || eq_cstr ("-liv", arg)) {
      livelock_ofile.open("/dev/stdout");
    }
    else if (eq_cstr ("-unknown", arg) || eq_cstr ("-unk", arg)) {
      unknown_ofile.open("/dev/stdout");
    }
    else if (eq_cstr ("-o-silent", arg) || eq_cstr ("-o-sil", arg)) {
      arg = argv[argi++];
      if (!arg)  failout_sysCx("Give a file for -o-silent!");
      silent_ofile.open(arg);
      if (!silent_ofile.good())
        failout_sysCx("Cannot open file for -o-silent!");
    }
    else if (eq_cstr ("-o-livelock", arg) || eq_cstr ("-o-liv", arg)) {
      arg = argv[argi++];
      if (!arg)  failout_sysCx("Give a file for -o-livelock!");
      livelock_ofile.open(arg);
      if (!livelock_ofile.good())
        failout_sysCx("Cannot open file for -o-livelock!");
    }
    else if (eq_cstr ("-o-unknown", arg) || eq_cstr ("-o-unk", arg)) {
      arg = argv[argi++];
      if (!arg)  failout_sysCx("Give a file for -o-unknown!");
      unknown_ofile.open(arg);
      if (!unknown_ofile.good())
        failout_sysCx("Cannot open file for -o-unknown!");
    }
    else if (eq_cstr ("-domsz", arg)) {
      arg = argv[argi++];
      if (!arg) {failout_sysCx("Give a file for -domsz!");}
      if (!fildesh_parse_unsigned(&domsz, arg) || domsz == 0)
        failout_sysCx("Usage: -domsz <domsz>\nWhere <domsz> is a positive integer.");
    }
    else if (max_period == 0) {
      if (!fildesh_parse_unsigned(&max_period, arg) || max_period == 0)
        failout_sysCx("Failed to parse period.");
    }
    else if (min_period == 0) {
      min_period = max_period;
      if (!fildesh_parse_unsigned(&max_period, arg) || max_period < min_period)
        failout_sysCx("Failed to parse period.");
    }
    else {
      DBog1( "Unrecognized option: %s", arg );
      failout_sysCx (0);
    }
  }

  if (max_period == 0) {
    failout_sysCx("Please provide a maximum period.");
  }

  if (min_period == 0) {
    min_period = 1;
  }

  if (!in) {
    in = open_FildeshXF("-");
  }

  PFmlaCtx pfmla_ctx;
  Table<PFmlaVbl> vbls;
  if (domsz > 0 && use_bdds) {
    bdd_init_vbls(pfmla_ctx, vbls, max_period, domsz);
  }

  const bool summarize =
    (!silent_ofile && !livelock_ofile && !unknown_ofile);

  while (true) {
    Table<PcState> ppgfun;
    unsigned read_domsz = xget_b64_ppgfun(in, ppgfun);
    if (read_domsz == 0)  break;
    if (domsz == 0) {
      domsz = read_domsz;
      if (use_bdds) {
        bdd_init_vbls(pfmla_ctx, vbls, max_period, domsz);
      }
    }
    else if (domsz != read_domsz) {
      failout_sysCx ("Use one domain size for inputs.");
    }

    uint period = 0;
    if (use_bdds)
      period = bdd_classify(ppgfun, vbls,
                            min_period, max_period, domsz);
    else
      period = tile_classify(ppgfun, max_period, domsz);

    if (period == 0) {
      if (!!silent_ofile) {
        oput_b64_ppgfun(silent_ofile, ppgfun, domsz) << '\n';
      }
      else if (summarize) {
        ofile << "silent\n";
      }
    }
    else if (period <= max_period) {
      if (!!livelock_ofile) {
        oput_b64_ppgfun(livelock_ofile, ppgfun, domsz) << '\n';
      }
      else if (summarize) {
        ofile << "livelock\tperiod:" << period << '\n';
      }
    }
    else {
      if (!!unknown_ofile) {
        oput_b64_ppgfun(unknown_ofile, ppgfun, domsz) << '\n';
      }
      else if (summarize) {
        ofile << "unknown\n";
      }
    }
    if (line_flush) {
      ofile.flush();
    }
  }

  close_FildeshX(in);
  return 0;
}

END_NAMESPACE

int main(int argc, char** argv) {
  return PROTOCON_NAMESPACE::main(argc, argv);
}
