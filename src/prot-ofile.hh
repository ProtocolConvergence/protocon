
#ifndef PROT_OFILE_HH_
#define PROT_OFILE_HH_

#include "cx/ofile.hh"
#include "xnsys.hh"

#include "namespace.hh"

bool
oput_protocon_file (OFile& of, const Xn::Sys& sys,
                    const Xn::Net& o_topology,
                    const vector<uint>& actions,
                    bool use_espresso, const char* comment);
bool
oput_protocon_file (OFile& of, const Xn::Sys& sys, const vector<uint>& actions,
                    bool use_espresso, const char* comment);
bool
oput_protocon_file (OFile& of, const Xn::Sys& sys,
                    bool use_espresso, const char* comment);
bool
oput_protocon_file (const String& ofilename,
                    const Xn::Sys& sys, const Xn::Net& o_topology,  const vector<uint>& actions,
                    bool use_espresso, const char* comment);
bool
oput_protocon_file (const String& ofilename, const Xn::Sys& sys,
                    bool use_espresso, const char* comment);

END_NAMESPACE
#endif

