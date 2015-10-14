
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
           struct timespec endtime,
           unsigned long peak_mem)
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

  DoLegit( 0 ) {
    difftime.tv_sec = endtime.tv_sec - begtime.tv_sec;
    if (endtime.tv_nsec >= begtime.tv_nsec) {
      difftime.tv_nsec = endtime.tv_nsec - begtime.tv_nsec;
    }
    else {
      difftime.tv_sec -= 1;
      difftime.tv_nsec = 1000 * 1000 * 1000;
      difftime.tv_nsec -= begtime.tv_nsec - endtime.tv_nsec;
    }
    time_t diff = difftime.tv_sec;
    ofile.printf("Elapsed Time: %02uh%02um%02u.%03us\n",
                 (uint) (diff / 60 / 60),
                 (uint) (diff / 60 % 60),
                 (uint) (diff % 60),
                 (uint) (difftime.tv_nsec / 1000 / 1000));


    ofile
      << "Peak Memory: "
      << peak_mem / 1000000 << "." << peak_mem % 1000000
      << " MB"
      << ofile.endl();
  }
}

