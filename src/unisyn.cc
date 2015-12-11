
extern "C" {
#include "cx/syscx.h"
}
#include "cx/fileb.hh"
#include "cx/tuple.hh"
#include "prot-ofile.hh"
#include "prot-xfile.hh"
#include "xnsys.hh"
#include <array>
#include <vector>

using std::array;
using std::vector;

typedef uint PcState;

vector< array<PcState,3> > unidirectionalRingProtocolGenerator(vector< array<PcState,2> > legits){
  size_t M = legits.size();
	size_t gamma;
	bool gammaExists = false;
  int **L = NULL;
  int **G = NULL;
  vector<int> validToLinkTo;
  vector<int> invalidToLinkTo;
	vector< array<PcState,3> > actions;
  
  L = (int**) malloc(M * sizeof(int*));
  for(size_t i = 0; i < M; i++)  L[i] = (int*) calloc(M, sizeof(int));
  //first diamention is the source vertex, second is destination
  
  for(size_t i = 0; i < legits.size(); i++){
    L[legits[i][0]][legits[i][1]] = 1;
  }
	
	for(size_t i = 0; i < M; i++)
		if(L[i][i]){
			gamma = i;
			gammaExists = true;
			break;
		}
  
	if(!gammaExists) return actions;
	
  //~ Lprime = (int**) malloc(M * sizeof(*Lprime));
  //~ for(int i = 0; i < M; i++){
    //~ Lprime[i] = (int*) malloc(M * sizeof(int));
    //~ memcpy(Lprime[i], L[i], M * sizeof(int));
  //~ }
  
  //~ //determine the cycles in the graph to turn Lprime into the actual
  //~ //representation of Lprime
  //~ //To do this, we can just establish which vertidies have no out edges
  //~ vector<int> cyclicElements;
  //~ //this is just a easy hack to calculate Lprime correctly, but its 
  //~ //runtime is far from optimal.
  //~ for(int cLoop = 0; cLoop < M; cLoop++){//consistancy loop
    //~ bool modifiedMatrix = false;
    //~ for(int i = 0; i < M; i++){
      //~ bool outVerticies = false;
      //~ for(int j = 0; j < M && !outVerticies; j++) if(Lprime[i][j]) outVerticies = true;
      //~ if(!outVerticies){
        //~ for(int j = 0; j < M; j++) Lprime[j][i] = 0;
        //~ modifiedMatrix = true;
      //~ }
    //~ }
    //~ if(modifiedMatrix) break;
  //~ }
  //Lprime is now calculated.
  
  // --> maybe just figure out the different cycles?
  //search over each node from a start node, and each time the original
  //node is reached, the algorithm backtracks, marking each touched node
  //with a value unique to the original node.

  //Start initializing G
  G = (int**) malloc(M * sizeof(*G));
  for(size_t i = 0; i < M; i++){
    G[i] = (int*) malloc(M * sizeof(**G));
    memcpy(G[i], L[i], sizeof(**G) * M);
  }
  
	
  //Seperate out values in the tree and those not in the tree
  
  validToLinkTo.push_back(gamma);
  for(size_t i = 0; i < gamma; i++) invalidToLinkTo.push_back(i);
  for(size_t i = gamma+1; i < M; i++) invalidToLinkTo.push_back(i);
  
  //start pruning the graph to make it into a tree
  bool treeChanged = true;
  while(invalidToLinkTo.size() && treeChanged){
    treeChanged = false;
    for(size_t i = 0; i < invalidToLinkTo.size(); i++){
      for(size_t j = 0; j < validToLinkTo.size(); j++){
        if(G[i][j]){
          for(size_t k = 0; k < j; k++) G[i][k] = 0;
          for(size_t k = j+1; k < M; k++) G[i][k] = 0;
          validToLinkTo.push_back(invalidToLinkTo[i]);
          invalidToLinkTo.erase(invalidToLinkTo.begin() + i);
          i--;
          treeChanged = true;
        }
      }
    }
  }
  
  //If there are verticies which cannot link to the tree, just directly
  //connect them to root.
  for(size_t i = 0; i < invalidToLinkTo.size(); i++){
    memset(G[invalidToLinkTo[i]], 0, sizeof(**G) * M);
    G[invalidToLinkTo[i]][gamma] = 1;
  }
  
  //Now we have the tree, but not the values x-1 contains that are valid
  //for something to change.  The values are the inverse of the out 
  //edges of the respective vertex in L.
  
  for(uint i = 0; i < M; i++)
    for(uint j = 0; j < M; j++)
      if(G[i][j])
        for(uint k = 0; k < M; k++)
          if(!L[i][k])
            actions.push_back(array<PcState, 3>{k, i, j});
  
  return actions;
}

uint
ReadUniRing(const char* filepath, Xn::Sys& sys, vector< array<PcState,2> >& legits);
bool
WriteUniRing(const char* filepath, const Xn::Sys& sys, const vector< array<PcState,3> >& actions);

/** Execute me now!**/
int main(int argc, char** argv) {
  int argi = init_sysCx(&argc, &argv);

  if (argi + 1 > argc)
    failout_sysCx("Need at least one argument (an input file).");

  const char* in_filepath = argv[argi++];
  Xn::Sys sys; /// For I/O only.
  vector< array<PcState,2> > legits;
  uint domsz = ReadUniRing(in_filepath, sys, legits);
  if (domsz == 0)
    failout_sysCx(in_filepath);

  // (Debugging) Output all the legitimate readable states.
  printf("Legitimate states for P[i]:\n");
  for (uint i = 0; i < legits.size(); ++i) {
    printf("x[i-1]==%u && x[i]==%u\n", legits[i][0], legits[i][1]);
  }

  vector< array<PcState,3> > actions;
////////////////////////////////////////////////////////////////////////
	actions = unidirectionalRingProtocolGenerator(legits);
////////////////////////////////////////////////////////////////////////

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
ReadUniRing(const char* filepath, Xn::Sys& sys, vector< array<PcState,2> >& legits)
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

    legits.push_back(array<PcState,2>{state[0], state[1]});
  }

  return topo.vbl_symms[0].domsz;
}

/** Write a unidirectional ring protocol file.**/
  bool
WriteUniRing(const char* filepath, const Xn::Sys& sys, const vector< array<PcState,3> >& actions)
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

