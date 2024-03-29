#include <queue>
#include <vector>

#include <fildesh/ostream.hh>
#include <fildesh/string.hh>

#include "uniact.hh"
#include "unifile.hh"
#include "src/prot-ofile.hh"
#include "src/prot-xfile.hh"
#include "src/xnsys.hh"

#include "src/inline/slurp_file_to_string.hh"

#include "src/namespace.hh"

#ifdef DEBUG
template <class T>
void printSquareMatrix(T** matrix, int length){
  std::ostream& out = std::cerr;
  for(int i = 0; i < length; i++){
    for(int j = 0; j < length; j++){
      out << matrix[i][j] << '\t';
    }
    out << '\n';
  }
  out << '\n';
  out.flush();
}
#endif


size_t** allocSquareMatrix(size_t M){
  size_t **toReturn = (size_t**) malloc(M * sizeof(*toReturn));
  for(size_t i = 0; i < M; i++)
    toReturn[i] = (size_t*) calloc(M, sizeof(**toReturn));
  return toReturn;
}


size_t** copySquareMatrix(size_t **toCopy, size_t M){
  size_t **toReturn = allocSquareMatrix(M);
  for(size_t i = 0; i < M; i++)
    memcpy(toReturn[i], toCopy[i], M * sizeof(**toReturn));
  return toReturn;
}


void freeSquareMatrix(size_t **toFree, size_t M){
  for(size_t i = 0; i < M; i++) free(toFree[i]);
  free(toFree);
}


  std::vector<UniAct>
unidirectionalRingProtocolGenerator(std::vector<UniStep> legits, size_t M)
{
  size_t gamma = 0;
  bool gammaExists = false;
  size_t **L = NULL;
  size_t **Lprime = NULL;
  std::vector<UniAct> actions;

  L = allocSquareMatrix(M);
  //first diamention is the x-1 vertex value, second is x vertex valid value

  for(size_t i = 0; i < legits.size(); i++)
    L[legits[i][0]][legits[i][1]] = 1;

#ifdef DEBUG
  printSquareMatrix(L, M);
#endif

  for(size_t i = 0; i < M; i++)
    if(L[i][i]){
      gamma = i;
      gammaExists = true;
      break;
    }

  if(!gammaExists) return actions;

  std::cerr << "gamma is " << gamma << std::endl;

  //determine the cycles in the graph to turn L into the representation
  //of Lprime
  //To do this, we can just establish which verticies have no out edges
  //this is just a easy hack to calculate Lprime correctly, but its
  //runtime is far from optimal.
  Lprime = copySquareMatrix(L, M);

  bool modifiedMatrix = true;
  while(modifiedMatrix){//consistancy loop
    modifiedMatrix = false;
    for(size_t i = 0; i < M; i++){
      bool outVerticies = false;
      for(size_t j = 0; j < M; j++) if(Lprime[i][j]) outVerticies = true;
      if(outVerticies == false){
        for(size_t j = 0; j < M; j++){
          if(Lprime[j][i]){
            Lprime[j][i] = 0;
            modifiedMatrix = true;
          }
        }
      }
    }
  }
#ifdef DEBUG
  printSquareMatrix(Lprime, M);
#endif

  //Lprime is now calculated.

  std::vector<uint> tau(M);
  for (uint i = 0; i < M; ++i) {
    tau[i] = i;
  }

  std::queue<uint> tree_q;
  tree_q.push(gamma);

  while (!tree_q.empty()) {
    uint j = tree_q.front();
    tree_q.pop();
    for (uint i = 0; i < M; ++i) {
      if (i != gamma && tau[i] == i && Lprime[i][j]) {
        tau[i] = j;
        tree_q.push(i);
      }
    }
  }

  for (uint i = 0; i < M; ++i) {
    if (tau[i] == i) {
      tau[i] = gamma;
    }
  }

  // Now we have the tree tau.

  for (uint i = 0; i < M; i++)
    for (uint k = 0; k < M; k++)
      if (!Lprime[i][k] && tau[i] != k)
        actions.push_back(UniAct(i, k, tau[i]));

  freeSquareMatrix(L, M); L = NULL;
  freeSquareMatrix(Lprime, M); Lprime = NULL;

  return actions;
}

uint
ReadUniRing(const char* filepath, Xn::Sys& sys, std::vector<UniStep>& legits);

/** Execute me now!**/
int main(int argc, char** argv) {
  int argi = 1;
  std::ostream& info_out = std::cerr;

  if (argi + 1 > argc)
    failout_sysCx("Need at least one argument (an input file).");

  const char* in_filepath = argv[argi++];
  Xn::Sys sys; /// For I/O only.
  std::vector<UniStep> legits;
  uint domsz = ReadUniRing(in_filepath, sys, legits);
  if (domsz == 0)
    failout_sysCx(in_filepath);

  // (Debugging) Output all the legitimate readable states.
  info_out << "Legitimate states for P[i]:\n";
  for (const UniStep& legit_state : legits) {
    info_out
      << "x[i-1]==" << legit_state[0]
      << " && x[i]==" << legit_state[1]
      << '\n';
  }

  std::vector<UniAct> actions;
////////////////////////////////////////////////////////////////////////
  actions = unidirectionalRingProtocolGenerator(legits, domsz);
////////////////////////////////////////////////////////////////////////

  // (Debugging) Output all the synthesized acctions.
  info_out << "Synthesized actions for P[i]:\n";
  for (const UniAct& act : actions) {
    info_out
      << "x[i-1]==" << act[0]
      << " && x[i]==" << act[1]
      << " --> x[i]:=" << act[2]
      << '\n';
  }

  if (argi + 2 >= argc && 0 == strcmp("-o-list", argv[argi])) {
    const char* out_filepath = argv[argi+1];
    argi += 2;
    fildesh::ofstream list_out(out_filepath);
    oput_list(list_out, Table<UniAct>(actions));
  }
  else if (argi + 1 >= argc) {
    if (argi + 2 >= argc && 0 == strcmp("-o", argv[argi])) {
      argi += 1;
    }
    const char* out_filepath = argv[argi++];
    oput_protocon(out_filepath, Table<UniAct>(actions));
  }

  return 0;
}

/** Read a unidirectional ring specification.**/
  uint
ReadUniRing(const char* filepath, Xn::Sys& sys, std::vector<UniStep>& legits)
{
  legits.clear();
  sys.topology.lightweight = true;
  ProtoconFileOpt infile_opt;
  slurp_file_to_string(infile_opt.text, filepath);
  if (!ReadProtoconFile(sys, infile_opt))
    BailOut(0, "Cannot read file!");
  const Xn::Net& topo = sys.topology;

  // Do some ad-hoc checking that this is a unidirectional ring.
  if (sys.direct_pfmla.sat_ck())
    BailOut(0, "Should not have actions.");
  if (topo.pc_symms.sz() != 1) {
    DBog_luint(topo.pc_symms.sz());
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
  Table<uint> rvbl_indices(2);
  rvbl_indices[0] = pc.rvbls[0]->pfmla_idx;
  rvbl_indices[1] = pc.rvbls[1]->pfmla_idx;
  if (pc_symm.spec->wmap[0]==0)
    SwapT(uint, rvbl_indices[0], rvbl_indices[1]);

  // Get all legitimate states.
  P::Fmla legit_pf = pc.invariant;
  while (legit_pf.sat_ck()) {
    Table<uint> state(2);

    // Find a readable state of this process that fits the legitimate states.
    legit_pf.state(&state[0], rvbl_indices);

    // Remove the corresponding predicate formula from {legit_pf}.
    legit_pf -= topo.pfmla_ctx.pfmla_of_state(&state[0], rvbl_indices);

    legits.push_back(UniStep(state[0], state[1]));
  }

  return topo.vbl_symms[0].domsz;
}

END_NAMESPACE

int main(int argc, char** argv) {
  return PROTOCON_NAMESPACE::main(argc, argv);
}
