
#include <iostream>

#include "pf.hh"

#include "synhax.hh"
#include "xnsys.hh"

using std::ostream;

static std::ostream& DBogOF = std::cerr;

bool ConvergenceCk(XnSys& sys, const PF& xnRel)
{
  PF span0( sys.invariant );

  while (!span0.tautologyCk(true)) {
    PF span1( span0 | sys.preimage(xnRel, span0) );
    if (span1.equivCk(span0))  return false;
    span0 = span1;
  }
  return true;
}

ostream& OPut(ostream& of, const XnAct& act, const XnNet& topo)
{
  const XnPc& pc = topo.pcs[act.pcIdx];
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    if (i != 0)  of << " && ";
    of << topo.wvbl(act.pcIdx, i).name << "==" << act.w0[i];
  }
  for (uint i = 0; i < pc.rvbls.size(); ++i) {
    of << " && ";
    of << topo.rvbl(act.pcIdx, i).name << "==" << act.r0[i];
  }
  of << " -->";
  for (uint i = 0; i < pc.wvbls.size(); ++i) {
    of << ' ' << topo.wvbl(act.pcIdx, i).name << ":=" << act.w1[i] << ';';
  }
  return of;
}


bool AddConvergence(XnSys& sys)
{
  vector<uint> actions;

  XnNet& topo = sys.topology;
  const uint nPossibleActs = topo.nPossibleActs();

  for (uint i = 0; i < nPossibleActs; ++i) {
    bool add = true;

    XnAct act( topo.action(i) );
    PF actPF( topo.actionPF(i) );

    // Check for self-loops. This is an inefficient method,
    // but the check only happens once.
    if (add && (topo.preimage(actPF).equivCk(topo.image(actPF)))) {
      add = false;
      if (false) {
        OPut((DBogOF << "Action " << i << " is a self-loop: "), topo.action(i), topo) << '\n';
      }
    }

    // This action does not start in the invariant.
    if (add && !(sys.invariant & topo.preimage(actPF)).tautologyCk(false)) {
      add = false;
      if (false) {
        OPut((DBogOF << "Action " << i << " breaks closure: "), topo.action(i), topo) << '\n';
      }
    }

    if (add) {
      actions.push_back(i);
    }
  }

  PF xnRel;
  for (uint i = 0; i < actions.size(); ++i) {
    xnRel |= topo.actionPF(actions[i]);
  }
  if (!ConvergenceCk(sys, xnRel)) {
    DBog0("Weak convergence is impossible!");
    return false;
  }

  return false;
}

void BidirectionalRing(XnNet& topo, uint npcs, uint domsz)
{
  // Build a bidirectional ring where each process P_i
  // has variable m_i of domain size 3.
  for (uint i = 0; i < npcs; ++i) {
    char name[10];
    sprintf(name, "m%u", i);

    XnPc& pc = Grow1(topo.pcs);
    pc.addVbl(XnVbl(name, domsz));
    pc.addPriv((i+npcs-1) % npcs, 0);
    pc.addPriv((i+1) % npcs, 0);
  }
}

void InstMatching(XnSys& sys, uint npcs)
{
  XnNet& topo = sys.topology;
  BidirectionalRing(topo, npcs, 3);

  // Commit to using this topology.
  // MDD stuff is initialized.
  topo.commitInitialization();

  for (uint pcidx = 0; pcidx < npcs; ++pcidx) {
    const PFVbl mp = topo.pfVblR(pcidx, 0);
    const PFVbl mq = topo.pfVbl (pcidx, 0);
    const PFVbl mr = topo.pfVblR(pcidx, 1);

    // 0 = Self, 1 = Left, 2 = Right
    sys.invariant &=
      (mp == 1 && mq == 0 && mr == 2) || // ( left,  self, right)
      (mp == 2 && mq == 1           ) || // (right,  left,     X)
      (           mq == 2 && mr == 1);   // (    X, right,  left)
  }
}

int main(int argc, char** argv)
{
  int argi = 1;
  const uint NPs = 6;

  if (argi < argc) {
    printf("%s: No arguments supported!\n", argv[0]);
    return 1;
  }

  XnSys sys;
  XnNet& topo = sys.topology;
  InstMatching(sys, NPs);
  AddConvergence(sys);

  DBog0("Showing all variables");
  print_mvar_list(topo.pfCtx.mdd_ctx());

  PFCtx& ctx = topo.pfCtx;

  //   m0==0 && (m1==0 || m1==2) && m2==1 --> m1:=1
  //   m0==0 && (m1==0 || m1==2) && m2==1 && m1'==1
  PF pf =
    topo.pcs[1].actUnchanged &&
    (topo.pfVbl(0, 0) == 0 && 
     (topo.pfVbl(1, 0) == 0 || topo.pfVbl(1, 0) == 2) &&
     topo.pfVbl(2, 0) == 0 &&
     topo.pfVblPrimed(1, 0) == 1);

  // Build an array of variable indices to see (m_0, m_0', m_1, m_1', m_2, m_2').
  array_t* vars = array_alloc(uint, 0);
  array_insert_last(uint, vars, topo.pfVbl      (0, 0).idx); // m_0
  array_insert_last(uint, vars, topo.pfVblPrimed(0, 0).idx); // m_0'
  array_insert_last(uint, vars, topo.pfVbl      (1, 0).idx); // m_1
  array_insert_last(uint, vars, topo.pfVblPrimed(1, 0).idx); // m_1'
  array_insert_last(uint, vars, topo.pfVbl      (2, 0).idx); // m_2
  array_insert_last(uint, vars, topo.pfVblPrimed(2, 0).idx); // m_2'

  mdd_gen* gen;
  array_t* minterm;
  // Show all satisfying valuations of the variables for the formula stored in /acts/
  DBog0("Showing satisfying valuations on m_0, m_0', m_1, m_1', m_2, m_2' of /acts/");
  mdd_t* acts = pf.dup_mdd();
  foreach_mdd_minterm(acts, gen, minterm, vars) {
    for (uint i = 0; i < (uint) minterm->num; ++i) {
      uint x = array_fetch(uint, minterm, i);
      uint vidx = array_fetch(uint, vars, i);
      fprintf(stdout, " %s=%u", ctx.vbl(vidx).name.c_str(), x);
    }
    fputc('\n', stdout);
    array_free(minterm);
  }
  mdd_free(acts);
  array_free(vars);

  return 0;
}

