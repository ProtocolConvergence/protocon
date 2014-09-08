
#ifndef PLA_HH_
#define PLA_HH_

#include "cx/ofile.hh"
#include "xnsys.hh"

bool
oput_protocon_file (Cx::OFile& of, const Xn::Sys& sys, bool use_espresso, const vector<uint>& actions);
bool
oput_protocon_file (Cx::OFile& of, const Xn::Sys& sys, bool use_espresso);
bool
oput_protocon_file (const Cx::String& ofilename, const Xn::Sys& sys,
                    bool use_espresso, const vector<uint>& actions);
bool
oput_protocon_file (const Cx::String& ofilename, const Xn::Sys& sys,
                    bool use_espresso);

#endif

