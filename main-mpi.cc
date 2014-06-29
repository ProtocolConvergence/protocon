
#include <mpi.h>

extern "C" {
#include "cx/syscx.h"
}
#include "cx/fileb.hh"
#include <errno.h>

#include "opt.hh"
#include "pla.hh"
#include "search.hh"
#include "synthesis.hh"
#include "stabilization.hh"
#include "mpidissem.hh"

#define MpiTag_MpiDissem 1
#define MpiTag_Conflict 2

static MpiDissem* mpi_dissem = 0;


static
  void
set_term_flag (int sig)
{
  (void) sig;
  mpi_dissem->terminate();
}

static
  Bool
done_ck (void* dat)
{
  Cx::Table<uint> flat_conflicts;
  ConflictFamily& conflicts = *(ConflictFamily*) dat;

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
  while (mpi_dissem->xtest(flat_conflicts)) {
    conflicts.add_conflicts(flat_conflicts);
  }
  conflicts.flush_new_conflicts(flat_conflicts);
  for (uint i = 0; i < flat_conflicts.sz(); ++i) {
    *mpi_dissem << flat_conflicts[i];
  }
  mpi_dissem->maysend();
  return mpi_dissem->done_ck();
}

static
  void
complete_dissemination(ConflictFamily& conflicts)
{
  Cx::Table<uint> flat_conflicts;
  mpi_dissem->done_fo();
  /* DBog1("completing... %u", mpi_dissem->PcIdx); */
  while (mpi_dissem->xwait(flat_conflicts)) {
    /* DBog1("waiting... %u", mpi_dissem->PcIdx); */
    conflicts.add_conflicts(flat_conflicts);
  }
  /* DBog1("done... %u", mpi_dissem->PcIdx); */
}

// Forward declaration
bool
stabilization_search_init
  (SynthesisCtx& synctx,
   Xn::Sys& sys,
   Cx::LgTable<Xn::Sys>& systems,
   Cx::OFileB& log_ofile,
   AddConvergenceOpt& opt,
   const ProtoconFileOpt& infile_opt,
   const ProtoconOpt& exec_opt,
   Cx::Table< Cx::Table<uint> >& act_layers
   );

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
  Cx::Table< FlatSet<uint> > flat_conflicts;

  mpi_dissem = new MpiDissem(PcIdx, NPcs, MpiTag_MpiDissem, MPI_COMM_WORLD);

  signal(SIGINT, set_term_flag);
  signal(SIGTERM, set_term_flag);
  MPI_Info mpi_info;
  MPI_Info_create(&mpi_info);

  if (!initialize_conflicts(conflicts, flat_conflicts, exec_opt, global_opt,
                            PcIdx == 0))
  {
    return false;
  }
  conflicts.flush_new_conflicts();

  Sign good = 1;
  AddConvergenceOpt opt(global_opt);
  Cx::OFileB log_ofile;

  opt.sys_pcidx = PcIdx;
  opt.sys_npcs = NPcs;

  Xn::Sys sys;
  Cx::LgTable<Xn::Sys> systems;
  SynthesisCtx synctx( PcIdx, NPcs );
  synctx.conflicts = conflicts;

  Cx::Table< Cx::Table<uint> > act_layers;

  DoLegit( good, 0 ) {
    good = stabilization_search_init
      (synctx, sys, systems, log_ofile, opt, infile_opt, exec_opt, act_layers);
  }

  PartialSynthesis& synlvl = synctx.base_partial;
  synctx.done_ck_fn = done_ck;
  synctx.done_ck_mem = &synctx.conflicts;

  if (!good)
    mpi_dissem->terminate();

  DBog1( "BEGIN! %u", PcIdx );

  if (exec_opt.task == ProtoconOpt::VerifyTask)
  {
    for (uint i = PcIdx; i < exec_opt.xfilepaths.sz(); i += NPcs) {
      if (synctx.done_ck())  break;
      Xn::Sys sys;
      ProtoconFileOpt verif_infile_opt( infile_opt );
      verif_infile_opt.file_path = exec_opt.xfilepaths[i].cstr();
      *opt.log << "VERIFYING: " << verif_infile_opt.file_path << opt.log->endl();
      const bool lightweight = !exec_opt.conflicts_ofilepath;
      sys.topology.lightweight = lightweight;
      if (ReadProtoconFile(sys, verif_infile_opt)) {
        StabilizationCkInfo info;
        info.find_livelock_actions = !lightweight;
        if (stabilization_ck(*opt.log, sys, exec_opt.params[0].stabilization_opt, &info)) {
          solution_found = true;
          ret_actions = sys.actions;
          *opt.log << "System is stabilizing." << opt.log->endl();

          if (!!exec_opt.ofilepath) {
            Cx::String filepath( exec_opt.ofilepath + "." + i );
            *opt.log << "Writing system to: " << filepath  << opt.log->endl();
            Cx::OFileB ofb;
            ofb.open(filepath);
            oput_protocon_file(ofb, sys, exec_opt.use_espresso, sys.actions);
          }
        }
        else {
          *opt.log << "System NOT stabilizing." << opt.log->endl();
          if (!lightweight && info.livelock_exists) {
            //synctx.conflicts.add_conflict(FlatSet<uint>(sys.actions));
            synctx.conflicts.add_conflict(info.livelock_actions);
          }
        }
      }
    }
  }
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
      found = AddStabilization(actions, synlvl, opt);
    }

    if (synctx.done_ck())
    {}
    else if (found)
    {
      if (opt.solution_as_conflict) {
        FlatSet<uint> flat_actions( actions );
        conflicts.add_conflict(flat_actions);
      }
      if (!global_opt.try_all) {
        mpi_dissem->terminate();
      }
      else if (!!exec_opt.ofilepath) {
        Cx::OFileB ofb;
        ofb.open(exec_opt.ofilepath + "." + PcIdx + "." + trial_idx);
        oput_protocon_file (ofb, sys, exec_opt.use_espresso, actions);
      }
      solution_found = true;
      ret_actions = actions;
      *opt.log << "SOLUTION FOUND!" << opt.log->endl();
    }
    else {
      if (!synctx.conflicts.sat_ck())
        set_term_flag (1);
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

  complete_dissemination(synctx.conflicts);

  if (!!exec_opt.conflicts_ofilepath) {
    Cx::Table<uint> flattest_conflicts;
    synctx.conflicts.oput_conflict_sizes(*opt.log);
    opt.log->flush();
    if (PcIdx == 0) {
      synctx.conflicts.flush_new_conflicts();
      for (uint source_idx = 1; source_idx < NPcs; ++source_idx) {
        MPI_Status status;
        uint sz = 0;
        MPI_Probe(MPI_ANY_SOURCE, MpiTag_Conflict, MPI_COMM_WORLD, &status);
        MPI_Get_count (&status, MPI_UNSIGNED, (int*) &sz);
        flattest_conflicts.resize(sz);
        MPI_Recv(&flattest_conflicts[0], sz, MPI_UNSIGNED, MPI_ANY_SOURCE,
                 MpiTag_Conflict, MPI_COMM_WORLD, &status);
        synctx.conflicts.add_conflicts(flattest_conflicts);
        synctx.conflicts.flush_new_conflicts();
        synctx.conflicts.oput_conflict_sizes(*opt.log);
        opt.log->flush();
      }

      synctx.conflicts.trim(global_opt.max_conflict_sz);
      oput_conflicts(synctx.conflicts, exec_opt.conflicts_ofilepath);
    }
    else {
      synctx.conflicts.flush_new_conflicts(flattest_conflicts);
      uint sz = flattest_conflicts.sz();
      MPI_Send(&flattest_conflicts[0], sz, MPI_UNSIGNED, 0,
               MpiTag_Conflict, MPI_COMM_WORLD);
    }
  }

  int ret_pc;
  {
    int send_pc = solution_found ? (int)PcIdx : -1;
    ret_pc = send_pc;
    MPI_Allreduce(&send_pc, &ret_pc, MpiTag_MpiDissem,
                  MPI_INT, MPI_MAX, MPI_COMM_WORLD);
  }

  signal(SIGINT, SIG_DFL);
  signal(SIGTERM, SIG_DFL);
  delete mpi_dissem;
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
  ProtoconFileOpt infile_opt;
  ProtoconOpt exec_opt;
  Xn::Sys sys;
  sys.topology.lightweight = true;
  bool good =
    protocon_options
    (sys, argi, argc, argv, opt, infile_opt, exec_opt);
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

    if (!exec_opt.ofilepath.empty_ck())
    {
      Cx::OFileB ofb;
      ofb.open(exec_opt.ofilepath);
      oput_protocon_file (ofb, sys, exec_opt.use_espresso);
    }
  }
  else if (found_papc < 0 && PcIdx == 0) {
    DBog0("No solution found...");
  }
  DBogOF.flush();

  lose_sysCx ();
  return 0;
}

