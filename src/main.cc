
extern "C" {
#include "cx/syscx.h"
}

#include "stabilization.hh"
#include "synthesis.hh"
#include "prot-ofile.hh"
#include "graphviz.hh"
#include "udp-ofile.hh"
#include "cx/fileb.hh"
#include "opt.hh"
#include "search.hh"
#include "interactive.hh"

/** Execute me now!*/
int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);
  AddConvergenceOpt opt;
  ProtoconFileOpt infile_opt;
  ProtoconOpt exec_opt;
  Xn::Sys sys;
  DeclLegit( good );

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
    if (exec_opt.params.sz() > 1) {
      failout_sysCx ("The -verify mode does not allow -param flags!");
    }
    found =
      stabilization_search(sys.actions, infile_opt, exec_opt, opt);
  }
  else if (exec_opt.task == ProtoconOpt::MinimizeConflictsTask)
  {
    if (exec_opt.xfilepath.empty_ck()) {
      failout_sysCx ("Need to use input file with random or -minimize-conflicts method!");
    }
    stabilization_search(sys.actions, infile_opt, exec_opt, opt);
  }
  else {
    if (exec_opt.xfilepath.empty_ck()) {
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
    for (uint i = 0; i < sys.actions.size(); ++i) {
      const Xn::Net& topo = sys.topology;
      Xn::ActSymm act;
      topo.action(act, sys.actions[i]);
      //DBogOF << sys.actions[i] << ' ';
      OPut(DBogOF, act) << '\n';
    }
  }
  else {
    DBog0("No solution found...");
  }

  if (found || exec_opt.task == ProtoconOpt::NoTask) {
    Xn::Sys osys;
    osys.topology.featherweight = true;
    const Xn::Net* o_topology = &sys.topology;
    if (exec_opt.task == ProtoconOpt::NoTask) {
      ProtoconFileOpt file_opt = infile_opt;
      file_opt.constant_map = exec_opt.params[0].constant_map;
      ReadProtoconFile(osys, file_opt);
      o_topology = &osys.topology;
    }

    if (!exec_opt.model_ofilepath.empty_ck()) {
      Cx::OFileB ofb;
      Cx::OFile ofile;
      DoLegitLineP( ofile, "Open Promela file" )
        ofb.uopen(exec_opt.model_ofilepath);
      DoLegit( 0 )
        OPutPromelaModel(ofile, sys, *o_topology);
    }
    if (!exec_opt.graphviz_ofilepath.empty_ck()) {
      Cx::OFileB ofb;
      Cx::OFile ofile;
      DoLegitLineP( ofile, "Open GraphViz file" )
        ofb.uopen(exec_opt.graphviz_ofilepath);
      DoLegit( 0 )
        oput_graphviz_file (ofile, *o_topology);
    }
    if (!exec_opt.udp_ofilepath.empty_ck()) {
      Claim2( exec_opt.task ,==, ProtoconOpt::NoTask );
      Cx::OFileB ofb;
      Cx::OFile ofile;
      DoLegitLineP( ofile, "Open UDP file" )
        ofb.uopen(exec_opt.udp_ofilepath);
      DoLegit( 0 )
        oput_udp_file (ofile, sys, *o_topology);
    }
    if (!exec_opt.ofilepath.empty_ck())
    {
      oput_protocon_file (exec_opt.ofilepath,
                          sys, *o_topology,
                          sys.actions,
                          exec_opt.use_espresso,
                          exec_opt.argline.ccstr());
    }
  }
  DBogOF.flush();

  lose_sysCx ();

  if (!good)  return 1;

  if (exec_opt.task == ProtoconOpt::InteractiveTask)
    return 0;
  if (exec_opt.task == ProtoconOpt::NoTask)
    return 0;
  return found ? 0 : 2;
}

