
#include <mpi.h>

extern "C" {
#include "cx/syscx.h"
}
#include "cx/fileb.hh"

#include "opt.hh"
#include "search.hh"
#include "synthesis.hh"

class MpiRound
{
private:
  bool done;
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
    , tag(_tag)
    , comm(_comm)
    , PcIdx(_PcIdx)
  {
    if (PcIdx > 0)  hood.push((PcIdx-1)/2);
    if (2*PcIdx+1 < NPcs)  hood.push(2*PcIdx+1);
    if (2*PcIdx+2 < NPcs)  hood.push(2*PcIdx+2);
    if (NPcs - 1 - PcIdx != PcIdx &&
        (PcIdx == 0 || NPcs - 1 - PcIdx != (PcIdx-1)/2) &&
        NPcs - 1 - PcIdx != 2*PcIdx+1 &&
        NPcs - 1 - PcIdx != 2*PcIdx+2) {
      hood.push(NPcs - 1 - PcIdx);
    }
#if 0
    for (uint i = 0; i < NPcs; ++i) {
      hood.push((int)i);
    }
#endif

    payloads.grow(2*this->sz(), -1);
    requests.grow(2*this->sz(), MPI_REQUEST_NULL);
    statuses.grow(2*this->sz());
    for (uint i = 0; i < this->sz(); ++i) {
      MPI_Irecv (this->x_payload(i), 1, MPI_INT,
                 this->hood[i], tag, comm,
                 this->x_request(i));
    }
  }

  uint sz() const { return hood.sz(); }

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

    for (uint i = 0; i < this->sz(); ++i) {
      *this->o_payload(i) = x;
      MPI_Isend (this->o_payload(i), 1, MPI_INT,
                 this->hood[i], tag, comm,
                 this->o_request(i));
    }
  }

  bool ck() {
    if (done)  return true;
    if (this->sz() == 0) {
      done = true;
      return true;
    }
    int index = 0;
    int flag = 0;
    int stat =
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
    int stat =
    MPI_Waitall (this->sz(),
                 this->o_requests(),
                 MPI_STATUS_IGNORE);
    Claim( stat == MPI_SUCCESS );
    stat =
    MPI_Waitall (this->sz(),
                 this->x_requests(),
                 MPI_STATUS_IGNORE);
    Claim( stat == MPI_SUCCESS );
  }
};

static MpiRound* mpi_done_flag = 0;


static
  void
set_done_flag (int sig)
{
  (void) sig;
  mpi_done_flag->fo(mpi_done_flag->PcIdx);
}

static
  Bool
done_ck (void* dat)
{
  (void) dat;
  return mpi_done_flag->ck();
}

static
  bool
stabilization_search(vector<uint>& ret_actions,
                     const ProtoconFileOpt& infile_opt,
                     const ProtoconOpt& exec_opt,
                     const AddConvergenceOpt& global_opt,
                     const uint PcIdx,
                     const uint NPcs)
{
  bool solution_found = false;
  ConflictFamily conflicts;

  mpi_done_flag = new MpiRound(PcIdx, NPcs, 1, MPI_COMM_WORLD);

  signal(SIGINT, set_done_flag);
  signal(SIGTERM, set_done_flag);
  MPI_Info mpi_info;
  MPI_Info_create(&mpi_info);

  Sign good = 1;
  AddConvergenceOpt opt(global_opt);
  ConflictFamily working_conflicts = conflicts;
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

  for (uint i = 0; good && i < exec_opt.params.sz(); ++i) {
    ProtoconFileOpt param_infile_opt = infile_opt;
    const Cx::String& key = exec_opt.params[i].first;
    const uint& val = exec_opt.params[i].second;
    param_infile_opt.constant_map[key] = val;

    Xn::Sys& param_sys = systems.grow1();
    DoLegit(good, "reading param file")
      good = ReadProtoconFile(param_sys, param_infile_opt);
    DoLegit(good, "add param sys")
      good = synctx.add(param_sys);
  }

  if (!good)
    set_done_flag (1);

  DBog1( "BEGIN! %u", PcIdx );

  synctx.conflicts = working_conflicts;
  working_conflicts.clear();
  {
    Set<uint> impossible( synctx.conflicts.impossible_set );
    impossible &= Set<uint>(synlvl.candidates);
    if (!impossible.empty())
      synlvl.revise_actions(Set<uint>(), impossible);
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
      found = try_order_synthesis(actions, sys, tape);
    }
    else
    {
      found = AddConvergence(actions, sys, synlvl, opt);
    }

    if (synctx.done_ck())
    {}
    else if (found)
    {
      if (!global_opt.try_all)
        set_done_flag (1);
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

  signal(SIGINT, SIG_DFL);
  signal(SIGTERM, SIG_DFL);

  mpi_done_flag->complete();
  delete mpi_done_flag;
  return solution_found;
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
  fprintf(stderr, "Hello from %u / %u!\n", PcIdx, NPcs);
  MPI_Barrier (MPI_COMM_WORLD);
  fprintf(stderr, "Wah! from %u / %u!\n", PcIdx, NPcs);

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

  bool found =
    stabilization_search(sys.actions, infile_opt, exec_opt, opt, PcIdx, NPcs);

  lose_sysCx ();
  return 0;
}

