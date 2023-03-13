#include "pla.h"

static
  void
oput_pla_XnEVbl(FildeshO* out, const XnEVbl* x)
{
  const unsigned n = x->vbl->domsz;
  for (unsigned i = 0; i < n; ++i) {
    putc_FildeshO(out, (i == (unsigned) x->val) ? '1' : '0');
  }
}

static
  void
oput_pla_state_XnSys(FildeshO* out, const XnSys* sys, const luint sidx)
{
  const Bit legit = test_BitTable (sys->legit, sidx);
  luint idx = sidx;
  for (unsigned i = 0; i < sys->vbls.sz; ++i) {
    XnEVbl x;
    x.vbl = &sys->vbls.s[i];
    x.val = idx / x.vbl->stepsz;
    idx = idx % x.vbl->stepsz;
    putc_FildeshO(out, ' ');
    oput_pla_XnEVbl(out, &x);
  }
  putc_FildeshO(out, ' ');
  puts_FildeshO(out, legit ? "01" : "10");
}

static
  void
oput_pla_legit(FildeshO* out, const XnSys* sys)
{
  puts_FildeshO(out, ".mv ");
  print_int_FildeshO(out, (int)sys->vbls.sz + 1);
  puts_FildeshO(out, " 0");
  for (unsigned i = 0; i < sys->vbls.sz; ++i) {
    putc_FildeshO(out, ' ');
    print_int_FildeshO(out, (int)sys->vbls.s[i].domsz);
  }
  puts_FildeshO(out, " 2\n");
  for (unsigned i = 0; i < sys->nstates; ++i) {
    oput_pla_state_XnSys(out, sys, i);
    putc_FildeshO(out, '\n');
  }
  puts_FildeshO(out, ".e\n");
}

static
  void
oput_pla_XnRule (FildeshO* out, const XnRule* g, const XnSys* sys)
{
  const XnPc* pc = &sys->pcs.s[g->pc];
  for (unsigned i = 0; i < pc->vbls.sz; ++i) {
    XnEVbl x;
    x.vbl = &sys->vbls.s[pc->vbls.s[i]];
    x.val = g->p.s[i];
    putc_FildeshO(out, ' ');
    oput_pla_XnEVbl(out, &x);
  }
  for (unsigned i = 0; i < pc->nwvbls; ++i) {
    XnEVbl x;
    x.vbl = &sys->vbls.s[pc->vbls.s[i]];
    x.val = g->p.s[i];
    putc_FildeshO(out, ' ');
    oput_pla_XnEVbl(out, &x);
  }
}

static
  void
oput_pla_pc(FildeshO* out, const XnPc* pc, const XnSys* sys,
            const TableT(XnRule) rules)
{
  const unsigned pcidx = IdxEltTable (sys->pcs, pc);
  puts_FildeshO(out, ".mv ");
  print_int_FildeshO(out, (int)pc->vbls.sz + pc->nwvbls);
  puts_FildeshO(out, " 0");
  for (unsigned i = 0; i < pc->vbls.sz; ++i) {
    putc_FildeshO(out, ' ');
    print_int_FildeshO(out, (int)sys->vbls.s[pc->vbls.s[i]].domsz);
  }
  for (unsigned i = 0; i < pc->nwvbls; ++i) {
    putc_FildeshO(out, ' ');
    print_int_FildeshO(out, (int)sys->vbls.s[pc->vbls.s[i]].domsz);
  }
  putc_FildeshO(out, '\n');

  putc_FildeshO(out, '#');
  for (unsigned i = 0; i < pc->vbls.sz; ++i) {
    putc_FildeshO(out, ' ');
    puts_FildeshO(out, ccstr_of_AlphaTab(&sys->vbls.s[pc->vbls.s[i]].name));
  }
  for (unsigned i = 0; i < pc->nwvbls; ++i) {
    putc_FildeshO(out, ' ');
    puts_FildeshO(out, ccstr_of_AlphaTab(&sys->vbls.s[pc->vbls.s[i]].name));
    putc_FildeshO(out, '\'');
  }
  putc_FildeshO(out, '\n');

  for (unsigned i = 0; i < rules.sz; ++i) {
    const XnRule* g = &rules.s[i];
    if (g->pc == pcidx)
    {
      oput_pla_XnRule(out, g, sys);
      putc_FildeshO(out, '\n');
    }
  }
  puts_FildeshO(out, ".e\n");
}

  bool
do_pla_XnSys(const XnSys* sys, const TableT(XnRule) rules)
{
  FildeshO* out;
  if (false) {
    out = open_FildeshOF("legit0.esp");
    if (out) {
      oput_pla_legit(out, sys);
      close_FildeshO(out);
    }
  }

  out = open_FildeshOF("/dev/null");
  if (out) {
    oput_pla_legit(out, sys);
    close_FildeshO(out);
  }

  for (unsigned pcidx = 0; 0 && pcidx < sys->pcs.sz; ++pcidx) {
    out = open_FildeshOF("/dev/null");
    if (!out) {continue;}
    oput_pla_pc(out, &sys->pcs.s[pcidx], sys, rules);
    close_FildeshO(out);
  }
  return true;
}

