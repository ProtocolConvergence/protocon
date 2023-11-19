
#ifndef PROT_OFILE_HH_
#define PROT_OFILE_HH_

#include "cx/synhax.hh"

#include "namespace.hh"

bool
oput_protocon_file(
    std::ostream& out,
    const Xn::Sys& sys, const Xn::Net& o_topology, const vector<uint>& actions,
    const std::string& maybe_espresso,
    const char* comment);
bool
oput_protocon_file(
    std::ostream& out,
    const Xn::Sys& sys, const vector<uint>& actions,
    const std::string& maybe_espresso,
    const char* comment);
bool
oput_protocon_file(
    std::ostream& out,
    const Xn::Sys& sys,
    const std::string& maybe_espresso,
    const char* comment);
bool
oput_protocon_file(
    const std::string& ofilename,
    const Xn::Sys& sys, const Xn::Net& o_topology,  const vector<uint>& actions,
    const std::string& maybe_espresso,
    const char* comment);
bool
oput_protocon_file(
    const std::string& ofilename,
    const Xn::Sys& sys,
    const std::string& maybe_espresso,
    const char* comment);

END_NAMESPACE
#endif

