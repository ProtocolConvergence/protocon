
#ifndef PLA_HH_
#define PLA_HH_

#include "cx/synhax.hh"

#include "namespace.hh"

void
oput_pla_pc_acts (OFile& ofile, const Xn::PcSymm& pc_symm,
                  const Table<Xn::ActSymm>& acts);
bool
oput_pla_file (OFile& ofile, const Xn::Sys& sys);
bool
oput_pla_file (const String& ofilename, const Xn::Sys& sys);
bool
oput_protocon_pc_acts_espresso (OFile& ofile,
                                const Xn::PcSymm& pc_symm,
                                const Table<Xn::ActSymm>& acts);

END_NAMESPACE
#endif

