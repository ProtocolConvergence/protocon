
#ifndef PROT_OFILE_HH_
#define PROT_OFILE_HH_
#include <ostream>
#include <string>
#include <vector>

#include "namespace.hh"

bool
oput_protocon_file(
    std::ostream& out,
    const Xn::Sys& sys, const Xn::Net& o_topology,
    const std::vector<Action_id>& actions,
    std::string_view maybe_espresso,
    std::string_view comment);
bool
oput_protocon_file(
    std::ostream& out,
    const Xn::Sys& sys,
    const std::vector<Action_id>& actions,
    std::string_view maybe_espresso,
    std::string_view comment);
bool
oput_protocon_file(
    std::ostream& out,
    const Xn::Sys& sys,
    std::string_view maybe_espresso,
    std::string_view comment);
bool
oput_protocon_file(
    const std::string& ofilename,
    const Xn::Sys& sys, const Xn::Net& o_topology,
    const std::vector<Action_id>& actions,
    std::string_view maybe_espresso,
    std::string_view comment);
bool
oput_protocon_file(
    const std::string& ofilename,
    const Xn::Sys& sys,
    std::string_view maybe_espresso,
    std::string_view comment);

END_NAMESPACE
#endif

