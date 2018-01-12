
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

  const char* id_ofilename = 0;
  const char* graphviz_ofilename = 0;
  const char* prot_ofilename = 0;
  const char* svg_livelock_ofilename = 0;
  const char* list_ofilename = 0;

  C::XFile xfile_olay[1];
  C::XFile* xfile = stdin_XFile ();

  Table<PcState> ppgfun;
  Table<UniAct> acts;
  uint domsz = 0;
  uint domsz_override = 0;

  uint cutoff = 0;
  while (argi < argc) {
    const char* arg = argv[argi++];
    if (eq_cstr ("-id", arg)) {
      if (!argv[argi])
        failout_sysCx("Argument Usage: -id <id>");
      init_XFile_olay_cstr (xfile_olay, argv[argi++]);
      xfile = xfile_olay;
    }
    else if (eq_cstr ("-x-list", arg)) {
      if (!argv[argi])
        failout_sysCx("Argument Usage: -x-list <filename>");
      XFileB list_xfileb;
      xfile = list_xfileb.uopen(0, argv[argi++]);
      if (!xfile)
        failout_sysCx("Cannot open -x-list file.");
      domsz = xget_list(xfile, acts);
      if (domsz == 0)
        failout_sysCx ("Failed to read protocol.");
      xfile = 0;
    }
    else if (eq_cstr ("-domsz", arg)) {
      if (!xget_uint_cstr (&domsz_override, argv[argi++]) || domsz_override == 0)
        failout_sysCx("Argument Usage: -domsz <M>\nWhere <M> is a positive integer!");
    }
    else if (eq_cstr ("-cutoff", arg)) {
      if (!xget_uint_cstr (&cutoff, argv[argi++]) || cutoff == 0)
        failout_sysCx("Argument Usage: -cutoff <limit>\nWhere <limit> is a positive integer!");
    }
    else if (eq_cstr ("-o-id", arg)) {
      id_ofilename = argv[argi++];
      if (!id_ofilename)
        id_ofilename = "-";
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

  if (domsz_override > 0) {
    // Override domain size.
    if (xfile) {
      failout_sysCx ("-domsz only works with -x-list.");
    }
    if (domsz > domsz_override) {
      failout_sysCx ("The given -domsz is not large enough for the given protocol.");
    }
    domsz = domsz_override;
  }

  if (xfile) {
    // Protocol given as an ID.
    domsz = xget_b64_ppgfun(xfile, ppgfun);
    if (domsz == 0)
      failout_sysCx ("Failed to read protocol.");
    acts = uniring_actions_of(ppgfun);
  }
  else {
    // Protocol given as a list of actions.
    ppgfun = uniring_ppgfun_of(acts, domsz);
  }

  if (svg_livelock_ofilename) {
    Table<PcState> top, col;
    if (cutoff == 0) {
      failout_sysCx ("Must provide a -cutoff when using -o-svg-livelock.");
    }
    Trit livelock_exists =
      livelock_semick(cutoff, ppgfun, domsz, &top, &col);

    if (livelock_exists==Yes) {
      OFileB svg_ofileb;
      OFile svg_ofile( svg_ofileb.uopen(0, svg_livelock_ofilename) );
      oput_svg_livelock(svg_ofile, ppgfun, top, col, domsz);
    }
    else {
      DBog0("No livelock detected for given -cutoff.");
    }
  }

  if (prot_ofilename) {
    oput_protocon(prot_ofilename, acts, domsz);
  }

  if (id_ofilename) {
    OFileB id_ofileb;
    OFile id_ofile( id_ofileb.uopen(0, id_ofilename) );
    oput_b64_ppgfun(id_ofile, ppgfun, domsz);
    id_ofile << '\n';
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
