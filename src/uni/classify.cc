
extern "C" {
#include "cx/syscx.h"
}

#include "uniact.hh"
#include "unifile.hh"
#include "../pfmla.hh"

#include "cx/bittable.hh"
#include "cx/fileb.hh"
#include <algorithm>

#include "livelock.hh"

#include "../namespace.hh"


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
  uint
bdd_classify(const Table<UniAct>& acts, uint min_period, uint max_period)
{
  const uint domsz = uniring_domsz_of(acts);

  // Initialize formula variables.
  PFmlaCtx pfmla_ctx;
  Table<PFmlaVbl> vbls(1+max_period);
  for (uint i = 0; i < 1+max_period; ++i) {
    uint vbl_id = pfmla_ctx.add_vbl((String("x") << i), domsz);
    vbls[i] = pfmla_ctx.vbl(vbl_id);
  }

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
tile_classify(const Table<UniAct>& acts, uint max_period)
{
  const uint domsz = uniring_domsz_of(acts);
  Table<PcState> ppgfun = uniring_ppgfun_of(acts, domsz);
  Table<PcState> row;
  const Trit exists =
    livelock_semick(max_period, ppgfun, domsz, &row);
  if (exists == Nil)  return 0;
  if (exists == Yes)  return row.sz()-1;
  return max_period + 1;
}

/** Execute me now!**/
int main(int argc, char** argv) {
  int argi = init_sysCx(&argc, &argv);

  uint min_period = 0;
  uint max_period = 0;

  bool use_bdds = true;
  bool use_bits = false;
  bool use_list = false;

  C::XFile xfile_olay[1];
  C::XFile* xfile = stdin_XFile ();
  OFile ofile( stdout_OFile () );

  while (argi < argc) {
    const char* arg = argv[argi++];
    if (eq_cstr ("-id", arg)) {
      if (!argv[argi])
        failout_sysCx("Argument Usage: -id <id>");
      init_XFile_olay_cstr (xfile_olay, argv[argi++]);
      xfile = xfile_olay;
      use_bits = false;
      use_list = false;
    }
    else if (eq_cstr ("-list", arg)) {
      use_bits = false;
      use_list = true;
    }
    else if (eq_cstr ("-bits", arg)) {
      use_bits = true;
      use_list = false;
    }
    else if (eq_cstr ("-nobdd", arg)) {
      use_bdds = false;
    }
    else if (eq_cstr ("-cutoff", arg)) {
      // Ignored.
    }
    else if (max_period == 0) {
      if (!xget_uint_cstr (&max_period, arg) || max_period == 0)
        failout_sysCx("Failed to parse period.");
    }
    else if (min_period == 0) {
      min_period = max_period;
      if (!xget_uint_cstr (&max_period, arg) || max_period <= min_period)
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

  while (true) {
    Table<UniAct> acts;
    uint domsz = 0;
    if (use_bits) {
      BitTable actset;
      domsz = xget_actions(xfile, actset);
      if (domsz == 0)  break;
      acts = uniring_actions_of(actset);
    }
    else if (use_list) {
      domsz = xget_list(xfile, acts);
      if (domsz == 0)  break;
    }
    else {
      Table<PcState> ppgfun;
      domsz = xget_b64_ppgfun(xfile, ppgfun);
      if (domsz == 0)  break;
      acts = uniring_actions_of(ppgfun);
    }

     uint period = 0;
     if (use_bdds)
       period = bdd_classify(acts, min_period, max_period);
     else
       period = tile_classify(acts, max_period);

     if (period == 0)
       ofile << "silent";
     else if (period <= max_period)
       ofile << "livelock\tperiod:" << period;
     else
       ofile << "unknown";
     ofile << ofile.endl();

     // Keep looping only if we're reading bitstrings.
     if (use_list)  break;
  }

  lose_sysCx();
  return 0;
}

END_NAMESPACE

int main(int argc, char** argv) {
  return PROJECT_NAMESPACE::main(argc, argv);
}
