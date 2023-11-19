
#include "main-all.hh"

#include "graphviz.hh"
#include "udp-ofile.hh"
#include "pla.hh"
#include "interactive.hh"

#include "namespace.hh"

/** Execute me now!*/
int main(int argc, char** argv)
{
  using namespace PROTOCON_NAMESPACE;
  int argi = init_sysCx (&argc, &argv);
  DeclLegit( good );
  AddConvergenceOpt opt;
  ProtoconFileOpt infile_opt;
  ProtoconOpt exec_opt;
  Xn::Sys sys;

#ifndef __APPLE__
  struct timespec begtime, endtime;
  clock_gettime(CLOCK_MONOTONIC, &begtime);
#endif

  sys.topology.lightweight = true;
  DoLegitLine( "" )
    protocon_options
    (sys, argi, argc, argv, opt, infile_opt, exec_opt);

  if (!good)  failout_sysCx ("Bad args.");

  bool found = false;
  if (exec_opt.task == ProtoconOpt::NoTask) {
  }
  else if (exec_opt.task == ProtoconOpt::InteractiveTask) {
    interactive(sys);
  }
  else if (exec_opt.task == ProtoconOpt::VerifyTask) {
    if (exec_opt.instances.size() > 1) {
      failout_sysCx ("The -verify mode does not allow -param flags!");
    }
    found =
      stabilization_search(sys.actions, infile_opt, exec_opt, opt);
  }
  else if (exec_opt.task == ProtoconOpt::MinimizeConflictsTask)
  {
    if (exec_opt.xfilepath.empty()) {
      failout_sysCx ("Need to use input file with random or -minimize-conflicts method!");
    }
    stabilization_search(sys.actions, infile_opt, exec_opt, opt);
  }
  else {
    if (exec_opt.xfilepath.empty()) {
      failout_sysCx ("Need to use input file with random or rank/shuffle method!");
    }
    found =
      stabilization_search(sys.actions, infile_opt, exec_opt, opt);
  }

  if (exec_opt.task == ProtoconOpt::VerifyTask) {
    if (found) {
      DBog0( "Protocol is self-stabilizing!" );
    }
    else {
      DBog0( "Protocol is NOT self-stabilizing... :(" );
    }
  }
  else if (exec_opt.task == ProtoconOpt::InteractiveTask) {
  }
  else if (exec_opt.task == ProtoconOpt::NoTask) {
  }
  else if (found) {
    DBog0("Solution found!");
    if (exec_opt.ofilepath.empty()) {
      for (uint i = 0; i < sys.actions.size(); ++i) {
        const Xn::Net& topo = sys.topology;
        Xn::ActSymm act;
        topo.action(act, sys.actions[i]);
        //std::cerr << sys.actions[i] << ' ';
        OPut(std::cerr, act) << '\n';
      }
    }
  }
  else {
    DBog0("No solution found...");
  }
#ifndef __APPLE__
  clock_gettime(CLOCK_MONOTONIC, &endtime);
#endif

  if (found || exec_opt.task == ProtoconOpt::NoTask) {
    Xn::Sys osys;
    // Can't use featherweight with conflicts.
    //osys.topology.featherweight = true;
    osys.topology.lightweight = true;
    const Xn::Net* o_topology = &sys.topology;
    if (exec_opt.task == ProtoconOpt::NoTask) {
      ProtoconFileOpt file_opt = infile_opt;
      file_opt.constant_map = exec_opt.instances[0].constant_map;
      ReadProtoconFile(osys, file_opt);
      o_topology = &osys.topology;
    }

    if (!exec_opt.model_ofilepath.empty()) {
      fildesh::ofstream pml_out(exec_opt.model_ofilepath.c_str());
      if (pml_out.good()) {
        OPutPromelaModel(pml_out, sys, *o_topology);
      }
    }
    if (!exec_opt.graphviz_ofilepath.empty()) {
      fildesh::ofstream graphviz_out(exec_opt.graphviz_ofilepath.c_str());
      if (graphviz_out.good()) {
        oput_graphviz_file(graphviz_out, *o_topology);
      }
    }
    if (!exec_opt.udp_ofilepath.empty()) {
      Claim2( exec_opt.task ,==, ProtoconOpt::NoTask );
      fildesh::ofstream udp_out(exec_opt.udp_ofilepath.c_str());
      if (udp_out.good()) {
        if (exec_opt.only_udp_include) {
          oput_udp_include_file(udp_out, sys, *o_topology);
        }
        else {
          oput_udp_file(udp_out, sys, *o_topology);
        }
      }
    }
    if (!exec_opt.pla_ofilepath.empty()) {
      Claim2( exec_opt.task ,==, ProtoconOpt::NoTask );
      DoLegit( 0 )
        oput_pla_file(exec_opt.pla_ofilepath, sys);
    }
    if (!exec_opt.ofilepath.empty())
    {
      oput_protocon_file (exec_opt.ofilepath,
                          sys, *o_topology,
                          sys.actions,
                          exec_opt.use_espresso,
                          exec_opt.argline.c_str());
    }
  }
  std::cerr.flush();

#ifdef ENABLE_MEMORY_STATS
#ifndef __APPLE__
  if (!exec_opt.stats_ofilepath.empty() ||
      exec_opt.task == ProtoconOpt::SearchTask) {
    unsigned long peak = peak_memory_use_sysCx ();
    oput_stats (exec_opt, begtime, endtime, peak);
  }
#endif
#endif

  lose_sysCx ();

  if (!good)  return 1;

  if (exec_opt.task == ProtoconOpt::InteractiveTask)
    return 0;
  if (exec_opt.task == ProtoconOpt::NoTask)
    return 0;
  return found ? 0 : 2;
}

END_NAMESPACE

int main(int argc, char** argv)
{
  return PROTOCON_NAMESPACE::main(argc, argv);
}


