
extern "C" {
#include "cx/syscx.h"
}

#include "cx/fileb.hh"
#include "protoconfile.hh"
#include "xnsys.hh"

struct LCNode {
  bool legit;
  uint x_pd;
  uint x_id;
  uint x_sc;
};

struct LCGraph {
  Cx::LgTable<LCNode> nodes;
};


static
  bool
deadlock_freedom_ck(const Xn::Sys& sys)
{
  Sign good = 1;
  Cx::Table<uint> actions;
  const Xn::Net& topo = sys.topology;
  const Xn::PcSymm& pc_symm = topo.pc_symms[0];
  uint pcidx = 0;

  DoLegit( good, "No representative process." )
    good = pc_symm.representative(&pcidx);
  if (!good)  return false;

  const Xn::Pc& pc = topo.pcs[pcidx];
  Cx::PFmla silent_pfmla = ~pc.puppet_xn.pre();
  silent_pfmla.ensure_ctx(topo.pfmla_ctx);

  Cx::Table<uint> pfmla_vbl_idcs;
  Cx::Table<uint> state;
  for (uint ridx = 0; ridx < pc.rvbls.sz(); ++ridx) {
    pfmla_vbl_idcs.push(pc.rvbls[ridx]->pfmla_idx);
    state.push(0);
  }

  LCGraph lcgraph;
  while (silent_pfmla.sat_ck()) {
    Cx::PFmla silent1 = silent_pfmla.pick_pre();
    LCNode node;
    node.legit = pc.invariant.overlap_ck(silent1);
    silent1.state(&state[0], pfmla_vbl_idcs);
    node.x_pd = state[0];
    node.x_id = state[1];
    node.x_sc = state[2];
    lcgraph.nodes.push(node);

    silent1 = true;
    for (uint ridx = 0; ridx < pc.rvbls.sz(); ++ridx) {
      silent1 &= (topo.pfmla_vbl(*pc.rvbls[ridx]) == state[ridx]);
    }
    silent_pfmla -= silent1;

    DBog4("x[i-1]==%u  x[i]==%u  x[i+1]==%u  legit:%s",
          node.x_pd, node.x_id, node.x_sc,
          node.legit ? "true" : "false");
  }

  // TODO: write code here!
  // - Add edges in continuation graph (LCGraph)
  // - Check graph for cycles

  return true;
}

/** Execute me now!*/
int main(int argc, char** argv)
{
  const char* in_filepath = "examplesoln/ColorRing.protocon";
  int argi = (init_sysCx (&argc, &argv), 1);

  if (argi < argc) {
    in_filepath = argv[argi++];
  }
  if (argi < argc) {
    failout_sysCx ("Maximum of one argument!");
  }

  Xn::Sys sys;
  sys.topology.lightweight = true;
  ProtoconFileOpt infile_opt;
  infile_opt.text = textfile_AlphaTab (0, in_filepath);

  if (!ReadProtoconFile(sys, infile_opt))
    failout_sysCx ("Cannot read file!");

  bool exit_good = deadlock_freedom_ck(sys);

  lose_sysCx ();
  return exit_good ? 0 : 2;
}

