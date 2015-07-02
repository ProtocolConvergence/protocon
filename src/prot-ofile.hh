
#ifndef PROT_OFILE_HH_
#define PROT_OFILE_HH_

#include "cx/ofile.hh"
#include "xnsys.hh"

bool
oput_protocon_file (Cx::OFile& of, const Xn::Sys& sys,
                    const Xn::Net& o_topology,
                    const vector<uint>& actions,
                    bool use_espresso, const char* comment);
bool
oput_protocon_file (Cx::OFile& of, const Xn::Sys& sys, const vector<uint>& actions,
                    bool use_espresso, const char* comment);
bool
oput_protocon_file (Cx::OFile& of, const Xn::Sys& sys,
                    bool use_espresso, const char* comment);
bool
oput_protocon_file (const Cx::String& ofilename,
                    const Xn::Sys& sys, const Xn::Net& o_topology,  const vector<uint>& actions,
                    bool use_espresso, const char* comment);
bool
oput_protocon_file (const Cx::String& ofilename, const Xn::Sys& sys,
                    bool use_espresso, const char* comment);

#endif

