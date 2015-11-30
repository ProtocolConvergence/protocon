
extern "C" {
#include "cx/syscx.h"
}
#include "cx/fileb.hh"
#include "cx/tuple.hh"
#include "prot-ofile.hh"
#include "prot-xfile.hh"
#include "xnsys.hh"
#include <vector>

using Cx::Tuple;
using Cx::mk_Tuple;
using std::vector;

typedef uint PcState;

uint
ReadUniRing(const char* filepath, Xn::Sys& sys, vector< Tuple<PcState,2> >& legits);
bool
WriteUniRing(const char* filepath, const Xn::Sys& sys, const vector< Tuple<PcState,3> >& actions);


/** Execute me now!**/
int main(int argc, char** argv) {
  int argi = init_sysCx(&argc, &argv);

  if (argi + 1 > argc)
    failout_sysCx("Need at least one argument (an input file).");

  const char* in_filepath = argv[argi++];
  Xn::Sys sys; /// For I/O only.
  vector< Tuple<PcState,2> > legits;
  uint domsz = ReadUniRing(in_filepath, sys, legits);
  if (domsz == 0)
    failout_sysCx(in_filepath);

  // (Debugging) Output all the legitimate readable states.
  printf("Legitimate states for P[i]:\n");
  for (uint i = 0; i < legits.size(); ++i) {
    printf("x[i-1]==%u && x[i]==%u\n", legits[i][0], legits[i][1]);
  }

  vector< Tuple<PcState,3> > actions;
  // ... build this up ...
  // Here's a hard-coded protocol for Sum-Not-Two:
  actions.push_back(mk_Tuple<PcState>(0,2,1));
  actions.push_back(mk_Tuple<PcState>(1,1,2));
  actions.push_back(mk_Tuple<PcState>(2,0,1));

  // (Debugging) Output all the synthesized acctions.
  printf("Synthesized actions for P[i]:\n");
  for (uint i = 0; i < actions.size(); ++i) {
    printf("x[i-1]==%u && x[i]==%u --> x[i]:=%u\n", actions[i][0], actions[i][1], actions[i][2]);
  }


  const char* out_filepath = argv[argi];
  if (out_filepath) {
    ++ argi;
    WriteUniRing(out_filepath, sys, actions);
  }

  lose_sysCx();
  return 0;
}

/** Read a unidirectional ring specification.**/
  uint
ReadUniRing(const char* filepath, Xn::Sys& sys, vector< Tuple<PcState,2> >& legits)
{
  legits.clear();
  sys.topology.lightweight = true;
  ProtoconFileOpt infile_opt;
  infile_opt.text.moveq(textfile_AlphaTab (0, filepath));
  if (!ReadProtoconFile(sys, infile_opt))
    BailOut(0, "Cannot read file!");
  const Xn::Net& topo = sys.topology;

  // Do some ad-hoc checking that this is a unidirectional ring.
  if (sys.direct_pfmla.sat_ck())
    BailOut(0, "Should not have actions.");
  if (topo.pc_symms.sz() != 1) {
    DBog_ujint(topo.pc_symms.sz());
    BailOut(0, "Should have only one kind of process.");
  }
  if (topo.pcs.sz() < 2)
    BailOut(0, "Should have more than 1 process.");

  // Ensure the invariant is given inside the process definition.
  {
    P::Fmla invariant(true);
    for (uint i = 0; i < topo.pcs.sz(); ++i) {
      invariant &= topo.pcs[i].invariant;
    }
    if (!invariant.equiv_ck(sys.invariant))
      BailOut(0, "Please specify invariant in process definition.");
  }

  // Just look at process P[0].
  const Xn::PcSymm& pc_symm = topo.pc_symms[0];
  const Xn::Pc& pc = *pc_symm.membs[0];
  if (pc.wvbls.sz() != 1)
    BailOut(0, "Should write 1 variable.");
  if (pc.rvbls.sz() != 2)
    BailOut(0, "Should read-only 1 variable.");

  // Get references to this process's variables that can be
  // used in the context of the predicate formulas.
  Cx::Table<uint> rvbl_indices(2);
  rvbl_indices[0] = pc.rvbls[0]->pfmla_idx;
  rvbl_indices[1] = pc.rvbls[1]->pfmla_idx;
  if (pc_symm.wmap[0]==0)
    SwapT(uint, rvbl_indices[0], rvbl_indices[1]);

  // Get all legitimate states.
  P::Fmla legit_pf = pc.invariant;
  while (legit_pf.sat_ck()) {
    Cx::Table<uint> state(2);

    // Find a readable state of this process that fits the legitimate states.
    legit_pf.state(&state[0], rvbl_indices);

    // Remove the corresponding predicate formula from {legit_pf}.
    legit_pf -= topo.pfmla_ctx.pfmla_of_state(&state[0], rvbl_indices);

    legits.push_back(mk_Tuple<PcState>(state[0], state[1]));
  }

  return topo.vbl_symms[0].domsz;
}

/** Write a unidirectional ring protocol file.**/
  bool
WriteUniRing(const char* filepath, const Xn::Sys& sys, const vector< Tuple<PcState,3> >& actions)
{
  const Xn::Net& topo = sys.topology;
  const Xn::PcSymm& pc_symm = topo.pc_symms[0];

  vector<uint> enum_actions;
  for (uint i = 0; i < actions.size(); ++i) {
    Xn::ActSymm act;
    act.pc_symm = &pc_symm;
    act.vals << actions[i][0] << actions[i][1] << actions[i][2];

    if (pc_symm.wmap[0]==0)
      SwapT(uint, act.vals[0], act.vals[1]);
    enum_actions.push_back(topo.action_index(act));
  }
  return oput_protocon_file (filepath, sys, topo, enum_actions, false, 0);
}

