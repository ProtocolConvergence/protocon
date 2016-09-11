
extern "C" {
#include "cx/syscx.h"
}

#include "livelock.hh"
#include "unifile.hh"

#include "cx/bittable.hh"
#include "cx/fileb.hh"
#include "cx/table.hh"

#include "../namespace.hh"

int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);

  const char* graphviz_ofilename = 0;
  const char* prot_ofilename = 0;
  const char* svg_livelock_ofilename = 0;
  const char* list_ofilename = 0;

  uint cutoff = 15;
  while (argi < argc) {
    const char* arg = argv[argi++];
    if (eq_cstr ("-cutoff", arg)) {
      if (!xget_uint_cstr (&cutoff, argv[argi++]) || cutoff == 0)
        failout_sysCx("Argument Usage: -cutoff <limit>\nWhere <limit> is a positive integer!");
    }
    else if (eq_cstr ("-o-graphviz", arg) ||
             eq_cstr ("-o-gv", arg)) {
      graphviz_ofilename = argv[argi++];
      if (!graphviz_ofilename)
        graphviz_ofilename = "-";
    }
    else if (eq_cstr ("-o-prot", arg)) {
      prot_ofilename = argv[argi++];
      if (!prot_ofilename)
        prot_ofilename = "-";
    }
    else if (eq_cstr ("-o-svg-livelock", arg) ||
             eq_cstr ("-o-svg", arg)) {
      svg_livelock_ofilename = argv[argi++];
      if (!svg_livelock_ofilename)
        svg_livelock_ofilename = "-";
    }
    else if (eq_cstr ("-o-list", arg)) {
      list_ofilename = argv[argi++];
      if (!list_ofilename)
        list_ofilename = "-";
    }
    else {
      DBog1( "Unrecognized option: %s", arg );
      failout_sysCx (0);
    }
  }

  C::XFile* xfile = stdin_XFile ();
  Table<PcState> ppgfun;
  uint domsz = xget_b64_ppgfun(xfile, ppgfun);
  if (domsz == 0) {
    failout_sysCx (0);
  }
  const Table<UniAct> acts = uniring_actions_of(ppgfun);

  if (svg_livelock_ofilename) {
    Table<PcState> top, col;
    Trit livelock_exists =
      livelock_semick(cutoff, ppgfun, domsz, &top, &col);

    if (svg_livelock_ofilename && livelock_exists==Yes) {
      OFileB svg_ofileb;
      OFile svg_ofile( svg_ofileb.uopen(0, svg_livelock_ofilename) );
      oput_svg_livelock(svg_ofile, ppgfun, top, col, domsz);
    }
  }

  if (prot_ofilename) {
    oput_protocon(prot_ofilename, acts, domsz);
  }

  if (graphviz_ofilename) {
    OFileB graphviz_ofileb;
    OFile graphviz_ofile( graphviz_ofileb.uopen(0, graphviz_ofilename) );
    oput_graphviz(graphviz_ofile, acts);
  }

  if (list_ofilename) {
    OFileB list_ofileb;
    OFile list_ofile( list_ofileb.uopen(0, list_ofilename) );
    oput_list(list_ofile, acts);
  }

  lose_sysCx ();
  return 0;
}

END_NAMESPACE

int main(int argc, char** argv) {
  return PROJECT_NAMESPACE::main(argc, argv);
}
