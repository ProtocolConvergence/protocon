
#include <mpi.h>

extern "C" {
#include "cx/syscx.h"
}
#include "cx/fileb.hh"

#include "opt.hh"
#include "pla.hh"
#include "search.hh"
#include "synthesis.hh"

static
  int
egcd(int* ret_a, int* ret_b)
{
  int a = *ret_a;
  int b = *ret_b;
  int x = 0;
  int y = 1;
  int u = 1;
  int v = 0;
  while (a != 0) {
    int q = b / a;
    int r = b % a;
    b = a;
    a = r;
    int m = x - u * q;
    x = u;
    u = m;
    int n = y - v * q;
    y = v;
    v = n;
  }
  *ret_a = x;
  *ret_b = y;
  return b;
}

/**
 * a x % n = b
 */
static
  void
linear_congruence(Cx::Table<uint>& ans, uint a, uint n, uint b)
{
  int r = a,
      s = n;
  uint d = umod_int(egcd(&r, &s), n);
  uint n_div_d = n / d;
  if (0 != b % d)  return;
  uint x0 = umod_int(r * (int) b / (int)d, n);
  for (uint i = 0; i < d; ++i) {
    ans.push((x0 + i * n_div_d) % n);
  }
}

/**
 * Generalized Kautz graph topology of degree {degree}.
 * The {hood} parameter is filled by 2*{degree} nodes.
 * The first {degree} nodes are sources for arcs whose destination node is {vidx}.
 * The second {degree} nodes are destinations for arcs whose source node is {vidx}.
 */
static
  void
gkautz_hood(Cx::Table<uint>& hood, uint vidx, uint degree, uint n)
{
  // For arcs ending at node {vidx}, solve the following
  //   -(vidx + q) % n = i * degree % n
  // for
  //   q <- {1,...,degree}
  // to obtain each source node {i}.
  // Depending on {degree} and {n}, a single {q} may generate zero or multiple solutions,
  // but there are exactly {degree} solutions in total.
  for (uint q = 1; q <= degree; ++q) {
    Cx::Table<uint> ans;
    linear_congruence
      (ans, degree, n,
       umod_int (- (int)(vidx + q), n)
      );
    for (uint i = 0; i < ans.sz(); ++i) {
      hood.push(ans[i]);
      //DBog3("%0.2u %0.2u %u", ans[i], vidx, q);
    }
  }
  Claim2( hood.sz() ,==, degree );

  // For arcs beginning at node {vidx}, solve the following
  //   j = -(vidx * degree + q) % n
  // for
  //   q <- {1,...,degree}
  // to obtain each destination node {j}.
  // Each q gives a unique {j}.
  for (uint q = 1; q <= degree; ++q) {
    uint j = umod_int (-(int)(vidx * degree + q), n);
    hood.push(j);
    //DBog3("%0.2u %0.2u %u", vidx, j, q);
  }
  Claim2( hood.sz() ,==, 2*degree );
}

class MpiRound
{
private:
  bool done;
  uint degree;
  int value;
  int tag;
  MPI_Comm comm;
  Cx::Table<uint> hood;
  Cx::Table<int        > payloads;
  Cx::Table<MPI_Request> requests;
  Cx::Table<MPI_Status > statuses;
public:
  uint PcIdx;
public:

  MpiRound(uint _PcIdx, uint NPcs, int _tag, MPI_Comm _comm)
    : done(false)
    , degree(4)
    , value(-1)
    , tag(_tag)
    , comm(_comm)
    , PcIdx(_PcIdx)
  {
    if (NPcs <= degree) {
      degree = NPcs;
      for (uint i = 0; i < NPcs; ++i)  hood.push(i);
      for (uint i = 0; i < NPcs; ++i)  hood.push(i);
    }
    else {
      gkautz_hood(this->hood, PcIdx, degree, NPcs);
    }

    payloads.grow(2*this->sz(), -1);
    requests.grow(2*this->sz(), MPI_REQUEST_NULL);
    statuses.grow(2*this->sz());
    for (uint i = 0; i < this->sz(); ++i) {
      MPI_Irecv (this->x_payload(i), 1, MPI_INT,
                 this->x_hood(i), tag, comm,
                 this->x_request(i));
    }
  }

  uint sz() const { return this->degree; }

  int x_hood(uint i) { return hood[i]; }
  int o_hood(uint i) { return hood[this->sz() + i]; }
  int* x_payload(uint i) { return &payloads[i]; }
  int* o_payload(uint i) { return &payloads[this->sz() + i]; }
  int* x_payloads() { return this->x_payload(0); }
  int* o_payloads() { return this->o_payload(0); }
  MPI_Request* x_request(uint i) { return &requests[i]; }
  MPI_Request* o_request(uint i) { return &requests[this->sz() + i]; }
  MPI_Request* x_requests() { return this->x_request(0); }
  MPI_Request* o_requests() { return this->o_request(0); }
  MPI_Status* x_status(uint i) { return &statuses[i]; }
  MPI_Status* o_status(uint i) { return &statuses[this->sz() + i]; }
  MPI_Status* x_statuses() { return this->x_status(0); }
  MPI_Status* o_statuses() { return this->o_status(0); }

  void fo(int x) {
    if (!done)
      done = true;
    else
      return;

    this->value = x;
    for (uint i = 0; i < this->sz(); ++i) {
      *this->o_payload(i) = x;
      MPI_Isend (this->o_payload(i), 1, MPI_INT,
                 this->o_hood(i), tag, comm,
                 this->o_request(i));
    }
  }
  int of() const {
    return this->value;
  }

  bool ck() {
    if (done)  return true;
    if (this->sz() == 0) {
      done = true;
      return true;
    }
    int index = 0;
    int flag = 0;
      MPI_Testany (this->sz(),
                   x_requests(),
                   &index, &flag,
                   MPI_STATUS_IGNORE);
    if (flag == 0)  return false;
    this->fo(*this->x_payload(index));
    return true;
  }

  void complete() {
    if (this->sz() == 0)  return;
    if (!this->done) {
      this->fo(PcIdx);
    }
    MPI_Waitall (this->sz(),
                 this->o_requests(),
                 MPI_STATUS_IGNORE);
    MPI_Waitall (this->sz(),
                 this->x_requests(),
                 MPI_STATUS_IGNORE);
  }
};

static MpiRound* mpi_done_flag = 0;


static
  void
set_done_flag (int sig)
{
  (void) sig;
  mpi_done_flag->fo(-1);
}

static
  Bool
done_ck (void* dat)
{
  (void) dat;
  return mpi_done_flag->ck();
}

#define MpiTag_MpiRound 1
#define MpiTag_Conflict 2

static
  int
stabilization_search(vector<uint>& ret_actions,
                     const ProtoconFileOpt& infile_opt,
                     const ProtoconOpt& exec_opt,
                     const AddConvergenceOpt& global_opt,
                     const uint PcIdx,
                     const uint NPcs)
{
  bool solution_found = false;
  ConflictFamily conflicts;

  mpi_done_flag = new MpiRound(PcIdx, NPcs, MpiTag_MpiRound, MPI_COMM_WORLD);

  signal(SIGINT, set_done_flag);
  signal(SIGTERM, set_done_flag);
  MPI_Info mpi_info;
  MPI_Info_create(&mpi_info);

  if (global_opt.conflicts_xfilename)
  {
    Cx::XFileB conflicts_xf;
    conflicts_xf.open(global_opt.conflicts_xfilename);
    conflicts_xf >> conflicts;
    if (!conflicts_xf.good()) {
      DBog1( "Bad read from conflicts file: %s", global_opt.conflicts_xfilename );
      return false;
    }
    conflicts.trim(global_opt.max_conflict_sz);
    if (PcIdx == 0) {
       conflicts.oput_conflict_sizes(DBogOF);
    }
  }

  Cx::Table< FlatSet<uint> > flat_conflicts;
  if (exec_opt.task == ProtoconOpt::MinimizeConflictsTask) {
    conflicts.all_conflicts(flat_conflicts);
    Cx::Table< Cx::Table< FlatSet<uint> > > sized_conflicts;
    for (uint i = 0; i < flat_conflicts.sz(); ++i) {
      uint sz = flat_conflicts[i].sz();
      while (sz >= sized_conflicts.sz()) {
        sized_conflicts.grow1();
      }
      sized_conflicts[sz].push(flat_conflicts[i]);
    }
    flat_conflicts.clear();
    for (uint i = sized_conflicts.sz(); i > 0;) {
      --i;
      for (uint j = 0; j < sized_conflicts[i].sz(); ++j) {
        flat_conflicts.push(sized_conflicts[i][j]);
      }
    }
  }

  Sign good = 1;
  AddConvergenceOpt opt(global_opt);
  Cx::OFileB log_ofile;

  opt.sys_pcidx = PcIdx;
  opt.sys_npcs = NPcs;
  opt.random_one_shot = true;
  if (exec_opt.log_ofilename) {
    Cx::String ofilename( exec_opt.log_ofilename );
    ofilename += ".";
    ofilename += PcIdx;
    log_ofile.open(ofilename);
    opt.log = &log_ofile;
  }
  else if (NPcs > 1) {
    opt.log = &Cx::OFile::null();
  }
  //opt.log = &DBogOF;
  //opt.verify_found = false;

  Xn::Sys sys;
  DoLegit(good, "reading file")
    good =
    ReadProtoconFile(sys, infile_opt);

  Cx::LgTable<Xn::Sys> systems;
  SynthesisCtx synctx( PcIdx, NPcs );

  synctx.conflicts = conflicts;

  DoLegit(good, "initialization")
    good = synctx.init(sys, opt);

  PartialSynthesis& synlvl = synctx.base_inst;

  synctx.done_ck_fn = done_ck;

  Cx::Table< Cx::Table<uint> > act_layers;
  if (opt.search_method == opt.RankShuffleSearch)
  {
    DoLegit(good, "ranking actions")
      good =
      rank_actions (act_layers, sys.topology,
                    synlvl.candidates,
                    synlvl.hi_xn,
                    synlvl.hi_invariant);
  }

  for (uint i = 1; good && i < exec_opt.params.sz(); ++i) {
    ProtoconFileOpt param_infile_opt = infile_opt;
    param_infile_opt.constant_map = exec_opt.params[i].constant_map;

    Xn::Sys& param_sys = systems.grow1();
    DoLegit(good, "reading param file")
      good = ReadProtoconFile(param_sys, param_infile_opt);
    DoLegit(good, "add param sys")
      good = synctx.add(param_sys);
  }

  for (uint i = 0; good && i < exec_opt.params.sz(); ++i) {
    synlvl[i].no_conflict = !exec_opt.params[i].conflict_ck();
    synlvl[i].no_partial = !exec_opt.params[i].partial_ck();
  }

  if (!good)
    mpi_done_flag->fo(-1);

  DBog1( "BEGIN! %u", PcIdx );

  if (exec_opt.task == ProtoconOpt::MinimizeConflictsTask)
  {
    for (uint conflict_idx = PcIdx; conflict_idx < flat_conflicts.sz(); conflict_idx += NPcs) {
      uint old_sz = flat_conflicts[conflict_idx].sz();
      if (!synctx.done_ck() && old_sz > 1) {
        *opt.log
          << "pcidx:" << PcIdx
          << " conflict:" << conflict_idx << "/" << flat_conflicts.sz()
          << " sz:" << old_sz
          << opt.log->endl();

        uint new_sz =
          synlvl.add_small_conflict_set(flat_conflicts[conflict_idx]);

        *opt.log
          << "DONE: pcidx:" << PcIdx
          << " conflict:" << conflict_idx << "/" << flat_conflicts.sz()
          << " old_sz:" << old_sz << " new_sz:" << new_sz
          << opt.log->endl();
      }
    }

    synctx.conflicts.oput_conflict_sizes(*opt.log);
    Cx::Table<uint> flattest_conflicts;
    if (PcIdx == 0) {
      for (uint source_idx = 1; source_idx < NPcs; ++source_idx) {
        uint sz = 0;
        MPI_Status status;
        MPI_Recv(&sz, 1, MPI_UNSIGNED, source_idx,
                 MpiTag_Conflict, MPI_COMM_WORLD, &status);
        flattest_conflicts.resize(sz);
        MPI_Recv(&flattest_conflicts[0], sz, MPI_UNSIGNED, source_idx,
                 MpiTag_Conflict, MPI_COMM_WORLD, &status);
        uint i = 0;
        while (i < flattest_conflicts.sz()) {
          uint n = flattest_conflicts[i++];
          synctx.conflicts.add_conflict(FlatSet<uint>(&flattest_conflicts[i], n));
          i += n;
        }
        synctx.conflicts.oput_conflict_sizes(*opt.log);
      }
      conflicts = synctx.conflicts;

      conflicts.trim(global_opt.max_conflict_sz);
      if (global_opt.conflicts_ofilename)
        oput_conflicts (conflicts, global_opt.conflicts_ofilename);
    }
    else {
      synctx.conflicts.all_conflicts(flat_conflicts);
      for (uint i = 0; i < flat_conflicts.sz(); ++i) {
        flattest_conflicts.push(flat_conflicts[i].sz());
        for (uint j = 0; j < flat_conflicts[i].sz(); ++j) {
          flattest_conflicts.push(flat_conflicts[i][j]);
        }
      }
      uint sz = flattest_conflicts.sz();
      MPI_Send(&sz, 1, MPI_UNSIGNED, 0,
               MpiTag_Conflict, MPI_COMM_WORLD);
      MPI_Send(&flattest_conflicts[0], sz, MPI_UNSIGNED, 0,
               MpiTag_Conflict, MPI_COMM_WORLD);
    }
  }

  vector<uint> actions;
  if (exec_opt.task == ProtoconOpt::SearchTask)
  for (uint trial_idx = 0; !synctx.done_ck() && (opt.ntrials == 0 || trial_idx < opt.ntrials); ++trial_idx)
  {
    bool found = false;
    if (opt.search_method == opt.RankShuffleSearch)
    {
      PartialSynthesis tape( synlvl );
      vector<uint>& candidates = tape.candidates;
      candidates.clear();
      for (uint i = 0; i < act_layers.sz(); ++i) {
        uint off = candidates.size();
        for (uint j = 0; j < act_layers[i].sz(); ++j) {
          candidates.push_back(act_layers[i][j]);
        }
        synctx.urandom.shuffle(&candidates[off], act_layers[i].sz());
      }
      found = try_order_synthesis(actions, tape);
    }
    else
    {
      found = AddConvergence(actions, synlvl, opt);
    }

    if (synctx.done_ck())
    {}
    else if (found)
    {
      if (!global_opt.try_all)
        mpi_done_flag->fo(PcIdx);
      solution_found = true;
      ret_actions = actions;
      *opt.log << "SOLUTION FOUND!" << opt.log->endl();
    }

    synctx.conflicts.oput_conflict_sizes(*opt.log);
    if (opt.search_method == opt.RankShuffleSearch) {
      if (opt.log != &DBogOF) {
        DBogOF << "pcidx:" << PcIdx << " trial:" << trial_idx+1 << " actions:" << actions.size() << '\n';
      }
      *opt.log << "pcidx:" << PcIdx << " trial:" << trial_idx+1 << " actions:" << actions.size() << '\n';
    }
    else {
      if (opt.log != &DBogOF) {
        *opt.log << "pcidx:" << PcIdx << " trial:" << trial_idx+1 << " depth:" << synlvl.failed_bt_level << '\n';
      }
      DBogOF << "pcidx:" << PcIdx << " trial:" << trial_idx+1 << " depth:" << synlvl.failed_bt_level << '\n';
    }
    opt.log->flush();
    DBogOF.flush();

    if (!synctx.done_ck()) {
      Set<uint> impossible( synctx.conflicts.impossible_set );
      impossible &= Set<uint>(synlvl.candidates);
      if (!impossible.empty())
        synlvl.revise_actions(Set<uint>(), impossible);
    }
  }

  int ret_pc;
  {
    int send_pc = solution_found ? (int)PcIdx : -1;
    ret_pc = send_pc;
    MPI_Allreduce(&send_pc, &ret_pc, MpiTag_MpiRound,
                  MPI_INT, MPI_MAX, MPI_COMM_WORLD);
  }

  mpi_done_flag->complete();
  signal(SIGINT, SIG_DFL);
  signal(SIGTERM, SIG_DFL);
  delete mpi_done_flag;
  return ret_pc;
}

int main(int argc, char** argv)
{
  MPI_Init (&argc, &argv);
  int argi = (init_sysCx (&argc, &argv), 1);
  (void) argi;
  push_losefn_sysCx ((void (*) ()) MPI_Finalize);
  uint PcIdx = 0;
  uint NPcs = 1;
  MPI_Comm_rank (MPI_COMM_WORLD, (int*) &PcIdx);
  MPI_Comm_size (MPI_COMM_WORLD, (int*) &NPcs);

  AddConvergenceOpt opt;
  const char* modelFilePath = 0;
  ProtoconFileOpt infile_opt;
  const char* outfile_path = 0;
  ProtoconOpt exec_opt;
  Xn::Sys sys;
  bool good =
    protocon_options
    (sys, argi, argc, argv, opt, modelFilePath, infile_opt, outfile_path, exec_opt);
  if (!good)  failout_sysCx ("Bad args.");

  int found_papc =
    stabilization_search(sys.actions, infile_opt, exec_opt, opt, PcIdx, NPcs);
  if (found_papc == (int)PcIdx) {
    DBog1("Solution found! (By PcIdx %u)", PcIdx);
    for (uint i = 0; i < sys.actions.size(); ++i) {
      const Xn::Net& topo = sys.topology;
      Xn::ActSymm act;
      topo.action(act, sys.actions[i]);
      //DBogOF << sys.actions[i] << ' ';
      OPut(DBogOF, act) << '\n';
    }

    if (outfile_path)
    {
      Cx::OFileB ofb;
      ofb.open(outfile_path);
      oput_protocon_file (ofb, sys);
    }
  }
  else if (found_papc < 0 && PcIdx == 0) {
    DBog0("No solution found...");
  }
  DBogOF.flush();

  lose_sysCx ();
  return 0;
}

