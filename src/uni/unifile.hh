#ifndef UNIFILE_HH_
#define UNIFILE_HH_

#include "uniact.hh"
#include <ostream>

#include "../namespace.hh"

PcState
uniring_domsz_of(const Table<PcState>& ppgfun);
PcState
uniring_domsz_of(const Table<UniAct>& acts);
PcState
uniring_domsz_of(const BitTable& actset);
Table<PcState>
uniring_ppgfun_of(const Table<UniAct>& acts, uint domsz=0);
Table<PcState>
uniring_ppgfun_of(const BitTable& actset, uint domsz=0);
Table<UniAct>
uniring_actions_of(const Table<PcState>& ppgfun, uint domsz=0);
Table<UniAct>
uniring_actions_of(const BitTable& actset, uint domsz=0);
BitTable
uniring_actset_of(const Table<PcState>& ppgfun, uint domsz=0);

std::ostream& operator<<(std::ostream& of, const BitTable& bt);

std::ostream&
oput_b64_ppgfun(std::ostream& ofile, const Table<PcState>& ppgfun, uint domsz=0);
PcState
xget_b64_ppgfun(FildeshX* in, Table<PcState>& ppgfun);

PcState
xget_list(FildeshX* in, Table<UniAct>& acts);
void
oput_list(std::ostream& ofile, const Table<UniAct>& acts);

void
map_livelock_ppgs(void (*f) (void**, const UniAct&, uint, uint),
                  void** ctx,
                  const Table<PcState>& bot,
                  const Table<PcState>& col,
                  const Table<PcState>& ppgfun,
                  const uint domsz);

void
oput_uniring_invariant(std::ostream& ofile, const BitTable& set, const uint domsz,
                       const char* pfx = "", const char* delim = " || ");
void
oput_protocon(std::ostream& ofile, const Table<UniAct>& acts, uint domsz = 0);
void
oput_protocon(const char* ofilename,
              const Table<UniAct>& acts, uint domsz = 0);
void
oput_promela(std::ostream& ofile, const Table<UniAct>& acts, uint domsz);
void
oput_graphviz(std::ostream& ofile, const Table<UniAct>& acts);

void
oput_svg_livelock(std::ostream& ofile, const Table<PcState>& ppgfun,
                  const Table<PcState>& bot,
                  const Table<PcState>& col,
                  const PcState domsz);

END_NAMESPACE
#endif
