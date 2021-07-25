
#ifndef PLA_HH_
#define PLA_HH_

#include "cx/synhax.hh"

#include "namespace.hh"

void
oput_pla_pc_acts(std::ostream& ofile, const Xn::PcSymm& pc_symm,
                 const Table<Xn::ActSymm>& acts);
bool
oput_pla_file(std::ostream& ofile, const Xn::Sys& sys);
bool
oput_pla_file(const String& ofilename, const Xn::Sys& sys);
bool
oput_protocon_pc_acts_espresso(std::ostream& ofile,
                               const Xn::PcSymm& pc_symm,
                               const Table<Xn::ActSymm>& acts);

END_NAMESPACE
#endif

