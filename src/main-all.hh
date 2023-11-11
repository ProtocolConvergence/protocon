
#include <ctime>
#include <iomanip>
#include <sstream>

#include <fildesh/ostream.hh>

#include "opt.hh"
#include "prot-ofile.hh"
#include "search.hh"
#include "stabilization.hh"
#include "synthesis.hh"

extern "C" {
#include "cx/syscx.h"
#ifdef ENABLE_MEMORY_STATS
#include "cx/benchmark.h"
#endif
}
#include "namespace.hh"

  void
oput_stats(const ProtoconOpt& exec_opt,
           struct timespec begtime,
           struct timespec endtime,
           unsigned long peak_mem)
{
  if (exec_opt.stats_ofilepath.empty_ck()) {return;}
  fildesh::ofstream stats_out(exec_opt.stats_ofilepath.ccstr());

  if (!stats_out.good()) {return;}

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
  time_t diff = difftime.tv_sec;

  std::stringstream stats_ss;
  stats_ss
    << "Elapsed Time: "
    << std::setfill('0') << std::setw(2)
    << (diff / 60 / 60) << "h"
    << (diff / 60 % 60) << "m"
    << (diff % 60) << "."
    << std::setfill('0') << std::setw(3)
    << (difftime.tv_nsec / 1000 / 1000) << "s\n";
  stats_out
    << stats_ss.str()
    << "Peak Memory: "
    << peak_mem / 1000000 << "." << peak_mem % 1000000
    << " MB"
    << std::endl;
}

END_NAMESPACE

