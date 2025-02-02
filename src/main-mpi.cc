#include <errno.h>
#include <signal.h>

#include <mpi.h>
#include <fildesh/string.hh>

#include "main-all.hh"
#include "mpidissem.hh"

#include "namespace.hh"

using Cx::MpiDissem;

#define MpiTag_MpiDissem 1
#define MpiTag_Conflict 2

#define DissemTag_Conflict 0
#define DissemTag_NLayers 1

static MpiDissem* mpi_dissem = 0;


static
  void
set_term_flag (int sig)
{
  (void) sig;
  mpi_dissem->terminate();
}

static
  void
handle_dissem_msg(MpiDissem::Tag tag,
                  const Table<uint>& msg,
                  SynthesisCtx& synctx)
{
  if (tag == DissemTag_Conflict) {
    synctx.conflicts.add_conflicts(msg);
  }
  else if (tag == DissemTag_NLayers) {
    if ((synctx.optimal_nlayers_sum == 0 && msg[0] > 0)
        ||
        (0 < msg[0] && msg[0] < synctx.optimal_nlayers_sum))
    {
      synctx.optimal_nlayers_sum = msg[0];
      mpi_dissem->push(tag, msg);
    }
  }
  else {
    Claim( 0 && "Unknown dissemination tag!");
  }
}

static
  bool
done_ck (void* dat)
{
  Table<uint> msg;
  SynthesisCtx& synctx = *(SynthesisCtx*) dat;

  if (0 == remove("kill-protocon")) {
    mpi_dissem->terminate();
    return 1;
  }
  else {
    errno = 0;
  }

  if (mpi_dissem->done_ck()) {
    return 1;
  }
  MpiDissem::Tag tag = 0;
  while (mpi_dissem->xtest(tag, msg)) {
    handle_dissem_msg (tag, msg, synctx);
  }
  synctx.conflicts.flush_new_conflicts(msg);
  if (msg.sz() > 0) {
    mpi_dissem->push(DissemTag_Conflict, msg);
  }
  mpi_dissem->maysend();
  return mpi_dissem->done_ck();
}

// Forward declaration
bool
stabilization_search_init
  (SynthesisCtx& synctx,
   Xn::Sys& sys,
   LgTable<Xn::Sys>& systems,
   AddConvergenceOpt& opt,
   const ProtoconFileOpt& infile_opt,
   const ProtoconOpt& exec_opt,
   Table< Table<uint> >& act_layers);

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
  uint solution_nlayers_sum = 0;
  ConflictFamily conflicts;
  Table< FlatSet<uint> > flat_conflicts;

  mpi_dissem = new MpiDissem(MpiTag_MpiDissem, MPI_COMM_WORLD);

  signal(SIGINT, set_term_flag);
  signal(SIGTERM, set_term_flag);

  if (!initialize_conflicts(conflicts, flat_conflicts, exec_opt, global_opt,
                            PcIdx == 0))
  {
    return false;
  }
  conflicts.flush_new_conflicts();

  DeclLegit( good );
  AddConvergenceOpt opt(global_opt);

  opt.sys_pcidx = PcIdx;
  opt.sys_npcs = NPcs;

  Xn::Sys sys;
  LgTable<Xn::Sys> systems;
  SynthesisCtx synctx( PcIdx, NPcs );
  synctx.conflicts = conflicts;
  std::ostream& log_out = synctx.log;

  Table< Table<uint> > act_layers;

  DoLegitLine( "Could not initialize." )
    stabilization_search_init
    (synctx, sys, systems, opt, infile_opt, exec_opt, act_layers);

  PartialSynthesis& synlvl = synctx.base_partial;
  synctx.done_ck_fn = done_ck;
  synctx.done_ck_mem = &synctx;

  if (!good)
    mpi_dissem->terminate();

  DBog1( "BEGIN! %u", PcIdx );

  if (exec_opt.task == ProtoconOpt::VerifyTask)
  {
    for (uint i = PcIdx; i < exec_opt.xfilepaths.size(); i += NPcs) {
      if (synctx.done_ck())  break;
      multi_verify_stabilization
        (i, synctx, ret_actions,
         solution_found,
         infile_opt, exec_opt, opt);
    }
  }
  if (exec_opt.task == ProtoconOpt::MinimizeConflictsTask)
  {
    for (uint conflict_idx = PcIdx; conflict_idx < flat_conflicts.sz(); conflict_idx += NPcs) {
      uint old_sz = flat_conflicts[conflict_idx].sz();
      if (!synctx.done_ck() && old_sz > 1) {
        log_out
          << "pcidx:" << PcIdx
          << " conflict:" << conflict_idx << "/" << flat_conflicts.sz()
          << " sz:" << old_sz
          << std::endl;

        uint new_sz =
          synlvl.add_small_conflict_set(flat_conflicts[conflict_idx]);

        log_out
          << "DONE: pcidx:" << PcIdx
          << " conflict:" << conflict_idx << "/" << flat_conflicts.sz()
          << " old_sz:" << old_sz << " new_sz:" << new_sz
          << std::endl;
      }
    }
  }

  if (exec_opt.task == ProtoconOpt::SearchTask)
  for (uint trial_idx = 0; !synctx.done_ck() && (opt.ntrials == 0 || trial_idx < opt.ntrials); ++trial_idx)
  {
    bool found = false;
    vector<uint> actions;
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
    else if (NPcs * trial_idx + PcIdx < global_opt.solution_guesses.sz()) {
      PartialSynthesis tape( synlvl );
      if (tape.pick_actions(global_opt.solution_guesses[NPcs * trial_idx + PcIdx])) {
        found = AddStabilization(actions, tape, opt);
      }
      synlvl.failed_bt_level = tape.failed_bt_level;
    }
    else
    {
      found = AddStabilization(actions, synlvl, opt);
    }

    if (found) {
      solution_found = true;
      ret_actions = actions;
      solution_nlayers_sum = synctx.optimal_nlayers_sum;

      if (!opt.optimize_soln)
        synctx.optimal_nlayers_sum = 0;
    }

    if (synctx.done_ck())
    {}
    else if (found)
    {
      log_out << "SOLUTION FOUND!" << std::endl;
      bool count_solution = true;
      if (opt.solution_as_conflict || global_opt.optimize_soln) {
        FlatSet<uint> flat_actions( actions );
        if (conflicts.conflict_ck(flat_actions)) {
          count_solution = false;
        }
        else {
          conflicts.add_conflict(flat_actions);
        }
      }

      if (global_opt.try_all && !exec_opt.ofilepath.empty() && count_solution) {
        fildesh::ostringstream oss;
        oss << exec_opt.ofilepath << "." << PcIdx << "." << trial_idx;
        fildesh::ofstream prot_out(oss.c_str());
        oput_protocon_file(prot_out, sys, actions,
                           exec_opt.maybe_espresso,
                           exec_opt.argline.c_str());
      }

      if (!count_solution) {
      }
      else if (synctx.opt.optimize_soln) {
        Table<uint> msg;
        msg.push(synctx.optimal_nlayers_sum);
        mpi_dissem->push(DissemTag_NLayers, msg);
      }
      else if (!global_opt.try_all) {
        mpi_dissem->terminate();
      }
    }
    else {
      if (!synctx.conflicts.sat_ck())
        set_term_flag (1);
    }

    synctx.conflicts.oput_conflict_sizes(log_out);

    for (std::ostream* ofile = &std::cerr;
         true;  // See end of loop.
         ofile = &log_out)
    {
      *ofile << "pcidx:" << PcIdx << " trial:" << trial_idx+1;

      if (opt.search_method == opt.RankShuffleSearch)
        *ofile
          << " actions:" << actions.size();
      else
        *ofile
          << " depth:" << synlvl.failed_bt_level
          << " nlayers_sum:" << synctx.optimal_nlayers_sum;

      *ofile << '\n';
      ofile->flush();

      if (ofile == &log_out)
        break;
    }

    if (!synctx.done_ck()) {
      Set<uint> impossible( synctx.conflicts.impossible_set );
      impossible &= Set<uint>(synlvl.candidates);
      if (!impossible.empty()) {
        if (!synlvl.revise_actions(Set<uint>(), impossible)) {
          // No solution exists.
          // Or no more solutions can be found.
          mpi_dissem->terminate();
        }
      }
    }
  }

  if (global_opt.try_all)
    mpi_dissem->terminate();

  mpi_dissem->finish();

  if (!exec_opt.conflicts_ofilepath.empty()) {
    Table<uint> flattest_conflicts;
    synctx.conflicts.oput_conflict_sizes(log_out);
    log_out.flush();
    if (PcIdx == 0) {
      synctx.conflicts.flush_new_conflicts();
      for (uint source_idx = 1; source_idx < NPcs; ++source_idx) {
        MPI_Status status;
        uint src_and_sz[2] = { 0, 0 };
        MPI_Recv(src_and_sz, 2, MPI_UNSIGNED,
                 MPI_ANY_SOURCE, MpiTag_Conflict, MPI_COMM_WORLD, &status);
        flattest_conflicts.resize(src_and_sz[1]);
        MPI_Recv(&flattest_conflicts[0], src_and_sz[1], MPI_UNSIGNED,
                 src_and_sz[0], MpiTag_Conflict, MPI_COMM_WORLD, &status);
        synctx.conflicts.add_conflicts(flattest_conflicts);
        synctx.conflicts.flush_new_conflicts();
        synctx.conflicts.oput_conflict_sizes(log_out);
        log_out.flush();
      }

      synctx.conflicts.trim(global_opt.max_conflict_sz);
      fildesh::ofstream conflict_out(exec_opt.conflicts_ofilepath.c_str());
      conflict_out << synctx.conflicts;
    }
    else {
      synctx.conflicts.flush_new_conflicts(flattest_conflicts);
      uint src_and_sz[2];
      src_and_sz[0] = PcIdx;
      src_and_sz[1] = flattest_conflicts.sz();
      MPI_Send(src_and_sz, 2, MPI_UNSIGNED, 0,
               MpiTag_Conflict, MPI_COMM_WORLD);
      MPI_Send(&flattest_conflicts[0], src_and_sz[1], MPI_UNSIGNED,
               0, MpiTag_Conflict, MPI_COMM_WORLD);
    }
  }

  int ret_pc;
  {
    int send_nlayers = solution_found ? (int)solution_nlayers_sum : -1;
    int max_nlayers = send_nlayers;
    MPI_Allreduce(&send_nlayers, &max_nlayers, 1,
                  MPI_INT, MPI_MAX, MPI_COMM_WORLD);

    if (!solution_found)
      send_nlayers = max_nlayers + 1;

    int min_nlayers = send_nlayers;
    MPI_Allreduce(&send_nlayers, &min_nlayers, 1,
                  MPI_INT, MPI_MIN, MPI_COMM_WORLD);

    if (min_nlayers == 0) {
      ret_pc = -1;
    }
    else {
      int send_pc = (send_nlayers == min_nlayers) ? (int)PcIdx : NPcs;
      ret_pc = send_pc;
      MPI_Allreduce(&send_pc, &ret_pc, 1,
                    MPI_INT, MPI_MIN, MPI_COMM_WORLD);
    }
  }

  signal(SIGINT, SIG_DFL);
  signal(SIGTERM, SIG_DFL);
  delete mpi_dissem;
  return ret_pc;
}

int main(int argc, char** argv)
{
  int argi = 1;
  DeclLegit( good );
  struct timespec begtime, endtime;
  uint PcIdx = 0;
  uint NPcs = 1;
  MPI_Comm_rank (MPI_COMM_WORLD, (int*) &PcIdx);
  MPI_Comm_size (MPI_COMM_WORLD, (int*) &NPcs);

  clock_gettime(CLOCK_MONOTONIC, &begtime);

  AddConvergenceOpt opt;
  ProtoconFileOpt infile_opt;
  ProtoconOpt exec_opt;
  Xn::Sys sys;

  sys.topology.lightweight = true;
  DoLegitLine( "" )
    protocon_options
    (sys, argi, argc, argv, opt, infile_opt, exec_opt);

  if (!good)  failout_sysCx ("Bad args.");

  int found_papc =
    stabilization_search(sys.actions, infile_opt, exec_opt, opt, PcIdx, NPcs);
  if (found_papc == (int)PcIdx) {
    DBog1("Solution found! (By PcIdx %u)", PcIdx);
    if (!exec_opt.ofilepath.empty())
    {
      oput_protocon_file (exec_opt.ofilepath, sys,
                          exec_opt.maybe_espresso,
                          exec_opt.argline.c_str());
    }
    else {
      for (uint i = 0; i < sys.actions.size(); ++i) {
        const Xn::Net& topo = sys.topology;
        Xn::ActSymm act;
        topo.action(act, sys.actions[i]);
        //std::cerr << sys.actions[i] << ' ';
        OPut(std::cerr, act) << '\n';
      }
    }
  }
  else if (found_papc < 0 && PcIdx == 0) {
    DBog0("No solution found...");
  }
  clock_gettime(CLOCK_MONOTONIC, &endtime);
  std::cerr.flush();

#ifdef ENABLE_MEMORY_STATS
  if (true) {
    unsigned long peak = peak_memory_use_sysCx ();
    unsigned long max_peak = 0;
    MPI_Reduce(&peak, &max_peak, 1,
               MPI_UNSIGNED_LONG, MPI_MIN, 0, MPI_COMM_WORLD);
    if (PcIdx==0) {
      oput_stats (exec_opt, begtime, endtime, max_peak);
    }
  }
#endif

  return good ? 0 : 1;
}

END_NAMESPACE

int main(int argc, char** argv)
{
  MPI_Init(&argc, &argv);
  int exstatus = PROTOCON_NAMESPACE::main(argc, argv);
  MPI_Finalize();
}
