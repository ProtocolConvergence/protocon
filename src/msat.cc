
extern "C" {
#include "cx/syscx.h"
#include "cx/fileb.h"
}
#define __STDC_LIMIT_MACROS
#define __STDC_FORMAT_MACROS
//#include <core/Solver.h>
#include <simp/SimpSolver.h>
#include <vector>
using std::vector;

#include "cx/alphatab.hh"
#include "prot-xfile.hh"
#include "prot-ofile.hh"
#include "conflictfamily.hh"
#include "synthesis.hh"

//#define WITH_PRE

int main(int argc, char** argv)
{
  int argi = (init_sysCx (&argc, &argv), 1);
  (void) argi;
  //const char filename[] = "examplespec/SumNotTwo.prot";
  //const char filename[] = "examplespec/ColorRing.prot";
  //const char filename[] = "examplespec/MatchRing.prot";
  const char filename[] = "examplespec/MatchRingThreeState.prot";
  //const char filename[] = "examplespec/Sat.prot";
  ConflictFamily conflicts;

  Xn::Sys sys;
  Xn::Net& topo = sys.topology;
  ProtoconFileOpt infile_opt;
  infile_opt.text.moveq
    (textfile_AlphaTab (0, filename));

  if (!ReadProtoconFile(sys, infile_opt)) {
    Claim( 0 && "Can't parse file" );
  }

  using namespace Minisat;
  SimpSolver solv;
  //solv.use_elim = false;
  //solv.use_asymm= false;
  const uint pre_offset = topo.n_possible_acts;
#ifdef WITH_PRE
  for (uint i = 0; i < topo.n_possible_acts + topo.total_pre_domsz; ++i)
#else
  for (uint i = 0; i < topo.n_possible_acts; ++i)
#endif
  {
    solv.newVar();
    solv.setFrozen(i, true);
  }

  vector<uint> candidates;
  Cx::Table<uint> dels;
  Cx::Table<uint> rejs;
  if (!candidate_actions(candidates, dels, rejs, sys)) {
    Claim( 0 && "No candidates apply!" );
  }

#define MTRUE false
#define MFALSE true

  vec<Lit> clause;
  for (uint i = 0; i < rejs.sz(); ++i) {
    solv.addClause(mkLit(rejs[i], MFALSE));
  }

  for (uint i = 0; i < dels.sz(); ++i) {
    solv.addClause(mkLit(dels[i], MFALSE));
  }

#if 0
  clause.clear();
  for (uint i = 0; i < candidates.size(); ++i) {
    clause.push(mkLit(candidates[i], MTRUE));
  }
  solv.addClause(clause);
#endif

#ifdef WITH_PRE
  Cx::Table< Cx::Table<uint> > pre_groups(topo.total_pre_domsz);
  for (uint i = 0; i < candidates.size(); ++i) {
    uint actidx = candidates[i];
    uint preidx = topo.action_pre_index(actidx);
    pre_groups[preidx].push(actidx);
    clause.clear();
    clause.push(mkLit(preidx + pre_offset, MTRUE));
    clause.push(mkLit(actidx, MFALSE));
    solv.addClause(clause);
  }

  for (uint i = 0; i < pre_groups.sz(); ++i) {
    clause.clear();
    clause.push(mkLit(i + pre_offset, MFALSE));
    for (uint j = 0; j < pre_groups[i].sz(); ++j) {
      clause.push(mkLit(pre_groups[i][j], MTRUE));
    }
    solv.addClause(clause);
  }
  pre_groups.clear();
#endif

  Cx::Set< Cx::Table<uint> > tried;
  for (uint i = 0; i < candidates.size(); ++i) {
    Xn::ActSymm act_i;
    topo.action(act_i, candidates[i]);
    for (uint j = i+1; j < candidates.size(); ++j) {
      Xn::ActSymm act_j;
      topo.action(act_j, candidates[j]);
      if (!coexist_ck(act_i, act_j, topo)) {
        clause.clear();
        clause.push(mkLit(candidates[i], MFALSE));
        clause.push(mkLit(candidates[j], MFALSE));
        solv.addClause(clause);
      }
    }
  }

  uint ntries = 0;
  while (solv.solve()) {
    X::Fmla xn(false);
    vector<uint> actions;
#ifdef WITH_PRE
    Cx::Table<bool> model(topo.n_possible_acts + topo.total_pre_domsz);
#else
    Cx::Table<bool> model(topo.n_possible_acts);
#endif
    for (uint i = 0; i < model.sz(); ++i) {
      model[i] = (l_True == solv.modelValue(i));
    }
    for (uint i = 0; i < topo.n_possible_acts; i++) {
      if (model[i]) {
        actions.push_back(i);
        //xn |= topo.action_pfmla(i);
      }
    }

    {
      Cx::Table<uint> tmp( actions );
      if (tried.elem_ck( tmp )) {
        DBog0("ALREADY TRIED");
      }
      tried << tmp;
    }
    StabilizationOpt opt;
    StabilizationCkInfo info;
    info.find_livelock_actions = true;
    if (stabilization_ck(Cx::OFile::null(), sys, opt, actions, &info)) {
      DBog0("solution found!");
      oput_protocon_file ("myoutput.prot", sys, actions, false, "from sat");
      break;
    }
    clause.clear();
    if (info.livelock_exists) {
      DBog0("livelock!");
      DBog_ujint(ntries);
      //for (uint i = 0; i < actions.size(); ++i) {
      //  clause.push(mkLit(actions[i], MFALSE));
      //}
      for (uint i = 0; i < info.livelock_actions.sz(); ++i) {
        clause.push(mkLit(info.livelock_actions[i], MFALSE));
      }
    }
    else {
      //DBog0("deadlock!");
#ifdef WITH_PRE
      for (uint i = pre_offset; i < model.sz(); ++i) {
        clause.push(mkLit(i, model[i] ? MFALSE : MTRUE));
      }
#else
      for (uint i = 0; i < candidates.size(); ++i) {
        clause.push(mkLit(candidates[i], model[candidates[i]] ? MFALSE : MTRUE));
      }
#endif
    }
    solv.addClause(clause);
    ++ntries;
    //DBog_ujint(ntries);
    if (!solv.okay()) {
      DBog0("not okay");
      DBog_ujint(ntries);
      break;
    }
  }

  lose_sysCx ();
  return 0;
}

