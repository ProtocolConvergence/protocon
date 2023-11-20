
#ifndef PLA_HH_
#define PLA_HH_
#include <ostream>
#include <string>
#include <vector>

#include "namespace.hh"

void
oput_pla_pc_acts(std::ostream& ofile, const Xn::PcSymm& pc_symm,
                 const std::vector<Xn::ActSymm>& acts);
bool
oput_pla_file(std::ostream& ofile, const Xn::Sys& sys);
bool
oput_pla_file(const std::string& ofilename, const Xn::Sys& sys);
bool
oput_protocon_pc_acts_espresso(
    std::ostream& out,
    const Xn::PcSymm& pc_symm,
    const std::vector<Xn::ActSymm>& acts,
    std::string_view espresso_name);

END_NAMESPACE
#endif

