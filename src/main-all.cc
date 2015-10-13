
#include <time.h>

extern "C" {
#include "cx/syscx.h"
#include "cx/benchmark.h"
}

#include "cx/fileb.hh"

#include "opt.hh"
#include "prot-ofile.hh"
#include "search.hh"
#include "stabilization.hh"
#include "synthesis.hh"

  void
oput_stats(const ProtoconOpt& exec_opt,
           struct timespec begtime,
           struct timespec endtime)
{
  DeclLegit( good );
  Cx::OFileB ofb;
  Cx::OFile ofile;
  if (!exec_opt.stats_ofilepath.empty_ck()) {
    DoLegitLineP( ofile, "Open stats file" )
      ofb.uopen(exec_opt.stats_ofilepath);
  }
  else {
    ofile = DBogOF;
  }

  struct timespec difftime;
  difftime.tv_sec = endtime.tv_sec - begtime.tv_sec;
  if (endtime.tv_nsec >= begtime.tv_nsec) {
    difftime.tv_nsec = endtime.tv_nsec - begtime.tv_nsec;
  }
  else {
    difftime.tv_sec -= 1;
    difftime.tv_nsec = 1000 * 1000 * 1000;
    difftime.tv_nsec -= begtime.tv_nsec - endtime.tv_nsec;
  }

  DoLegit( 0 ) {
    size_t peak = peak_memory_use_sysCx ();
    ofile
      << "Peak Memory: "
      << peak / 1000000 << "." << peak % 1000000
      << " MB"
      << ofile.endl();
  }
}

