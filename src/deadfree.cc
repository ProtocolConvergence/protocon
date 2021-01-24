
extern "C" {
#include "cx/syscx.h"
}

#include "cx/fileb.hh"
#include "prot-xfile.hh"
#include "xnsys.hh"
#include <queue>
#include <stack>

#include "namespace.hh"

struct LCNode {
  bool legit;
  uint x_pd;
  uint x_id;
  uint x_sc;
};

struct LCGraph {
  LgTable<LCNode> nodes;
  std::map<std::pair<uint, uint>, std::vector<uint> > edges;
};


static
  bool
deadlock_freedom_ck(const Xn::Sys& sys)
{
  DeclLegit( good );
  Table<uint> actions;
  const Xn::Net& topo = sys.topology;
  const Xn::PcSymm& pc_symm = topo.pc_symms[0];
  uint pcidx = 0;

  DoLegitLine( "No representative process." )
    pc_symm.representative(&pcidx);
  if (!good)  return false;

  const Xn::Pc& pc = topo.pcs[pcidx];
  P::Fmla silent_pfmla = ~pc.puppet_xn.pre();
  silent_pfmla.ensure_ctx(topo.pfmla_ctx);

  Table<uint> pfmla_vbl_idcs;
  Table<uint> state;
  for (uint ridx = 0; ridx < pc.rvbls.sz(); ++ridx) {
    pfmla_vbl_idcs.push(pc.rvbls[ridx]->pfmla_idx);
    state.push(0);
  }

  LCGraph lcgraph;
  while (silent_pfmla.sat_ck()) {
    P::Fmla silent1 = silent_pfmla.pick_pre();
    LCNode node;
    node.legit = pc.invariant.overlap_ck(silent1);
    silent1.state(&state[0], pfmla_vbl_idcs);
    node.x_pd = state[0];
    node.x_id = state[1];
    node.x_sc = state[2];

    lcgraph.edges[std::make_pair(node.x_pd, node.x_id)]
      .push_back(lcgraph.nodes.sz());
    lcgraph.nodes.push(node);

    silent1 = true;
    for (uint ridx = 0; ridx < pc.rvbls.sz(); ++ridx) {
      silent1 &= (topo.pfmla_vbl(*pc.rvbls[ridx]) == state[ridx]);
    }
    silent_pfmla -= silent1;

    //DBog4("x[i-1]==%u  x[i]==%u  x[i+1]==%u  legit:%s", node.x_pd,
    //node.x_id, node.x_sc, node.legit ? "true" : "false");
  }
  printf("\nThe size of the RCG graph in the protocol: [%lu]\n",
         lcgraph.nodes.sz());
  bool isDeadLock = false;

  for (uint sidx = 0; sidx < lcgraph.nodes.sz(); sidx++) {
    const LCNode &node = lcgraph.nodes[sidx];
    if (node.legit) {
      continue;
    }

    Set<uint> visited;
    std::queue<std::pair<uint, uint> > frontier;
    frontier.push(std::make_pair(sidx, 0));
    std::stack<LCNode> trace;
    std::stack<LCNode> traceoutput;

    while (!frontier.empty()) {
      bool finCheck = false;
      std::pair<uint, uint> tpair = frontier.front();
      uint t = tpair.first;
      uint tdistance = tpair.second;
      frontier.pop();
      const LCNode &tnode = lcgraph.nodes[t];

      const std::vector<uint> &next =
        lcgraph.edges[std::make_pair(tnode.x_id, tnode.x_sc)];
      if (next.size() != 0) {
        trace.push(lcgraph.nodes[t]);
      }

      for (uint nidx = 0; nidx < next.size(); nidx++) {
        if (sidx == next[nidx]) {

          LCNode termnode = lcgraph.nodes[next[nidx]];
          bool legit = false;
          while (!trace.empty()) {

            LCNode tracemnode = trace.top();
            if (termnode.x_pd == tracemnode.x_id
                && termnode.x_id == tracemnode.x_sc) {
              legit |= tracemnode.legit;
              traceoutput.push(tracemnode);
              termnode = tracemnode;
            }

            trace.pop();
          }

          while (!traceoutput.empty()) {
            printf("[RING TRACE] (x[i-1]==%u  x[i]==%u  x[i+1]==%u)  local-legitimate:[%s]\n",
                   traceoutput.top().x_pd, traceoutput.top().x_id,
                   traceoutput.top().x_sc,
                   traceoutput.top().legit ? "true" : "false");
            traceoutput.pop();
          }
          if (legit == 1) {
            finCheck = true;
            isDeadLock = true;
            printf("The protocol has a deadlock.\nThe global deadlock ring size is [%u]\n",
                   tdistance + 1);

            tdistance = 0;
          }
          break;

        }
        if (visited.elem_ck(next[nidx])) {
          continue;
        }
        visited << next[nidx];
        frontier.push(std::make_pair(next[nidx], tdistance + 1));

      }
      if (finCheck) {
        printf("----------------------------------\n");
        break;
      }
    }
  }
  if (!isDeadLock) {
    printf("The protocol does not have deadlock.\n");
  }
  return true;
}

/** Execute me now!**/
int main(int argc, char** argv) {
  int argi = init_sysCx(&argc, &argv);


  if (argi + 1 != argc)
    failout_sysCx("Need exactly one argument (an input file).");

  const char* in_filepath = argv[argi++];

  Xn::Sys sys;
  sys.topology.lightweight = true;
  ProtoconFileOpt infile_opt;

  // infile_opt.text = read_all_text(in_filepath)
  infile_opt.text.moveq(textfile_AlphaTab (0, in_filepath));

  if (!ReadProtoconFile(sys, infile_opt))
    failout_sysCx("Cannot read file!");

  bool exit_good = deadlock_freedom_ck(sys);
  lose_sysCx();
  return exit_good ? 0 : 2;
}

END_NAMESPACE

int main(int argc, char** argv) {
  return PROTOCON_NAMESPACE::main(argc, argv);
}

