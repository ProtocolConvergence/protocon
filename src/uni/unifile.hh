#ifndef UNIFILE_HH_
#define UNIFILE_HH_

#include "uniact.hh"

struct XFile;
namespace Cx {
  class OFileB;
  class XFileB;
}

#include "../namespace.hh"

namespace C {
  using ::XFile;
}
using Cx::OFileB;
using Cx::XFileB;

PcState
uniring_domsz_of(const Table<UniAct>& acts);
PcState
uniring_domsz_of(const BitTable& actset);
Table<UniAct>
uniring_actions_of(const BitTable& actset);

OFile& operator<<(OFile& of, const BitTable& bt);

PcState
xget_list(C::XFile* xfile, Table<UniAct>& acts);
void
oput_list(OFile& ofile, const Table<UniAct>& acts);
PcState
xget_actions(C::XFile* xfile, BitTable& actset);

void
map_livelock_ppgs(void (*f) (void**, const UniAct&, uint, uint),
                  void** ctx,
                  const Table<PcState>& bot,
                  const Table<PcState>& col,
                  const Table<PcState>& ppgfun,
                  const uint domsz);

void
oput_uniring_invariant(OFile& ofile, const BitTable& set, const uint domsz,
                       const char* pfx = "", const char* delim = " || ");
void
oput_protocon(OFile& ofile, const Table<UniAct>& acts, uint domsz = 0);
void
oput_protocon(const String& ofilename,
              const Table<UniAct>& acts, uint domsz = 0);
void
oput_promela(OFile& ofile, const Table<UniAct>& acts, uint domsz);
void
oput_graphviz(OFile& ofile, const Table<UniAct>& acts);

void
oput_svg_livelock(OFile& ofile, const Table<PcState>& ppgfun,
                  const Table<PcState>& bot,
                  const Table<PcState>& col,
                  const PcState domsz);

PcState
tilings_and_patterns_aperiodic_uniring(Table<UniAct>& acts);

END_NAMESPACE
#endif
