
#include <fildesh/ostream.hh>

#include "livelock.hh"
#include "unifile.hh"

#include "src/cx/bittable.hh"
#include "src/cx/table.hh"

#include "src/inline/eq_cstr.h"

extern "C" {
#include "src/cx/syscx.h"
}
#include "src/namespace.hh"

int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);

  const char* id_ofilename = 0;
  const char* graphviz_ofilename = 0;
  const char* prot_ofilename = 0;
  const char* svg_livelock_ofilename = 0;
  const char* list_ofilename = 0;

  FildeshX* in = NULL;

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
      close_FildeshX(in);
      in = open_FildeshXA();
      size_t n = strlen(argv[argi]);
      memcpy(grow_FildeshX(in, n), argv[argi], n);
      argi += 1;
    }
    else if (eq_cstr ("-x-list", arg)) {
      if (!argv[argi])
        failout_sysCx("Argument Usage: -x-list <filename>");
      in = open_FildeshXF(argv[argi++]);
      if (!in)
        failout_sysCx("Cannot open -x-list file.");
      domsz = xget_list(in, acts);
      if (domsz == 0)
        failout_sysCx ("Failed to read protocol.");
      close_FildeshX(in);
      in = NULL;
    }
    else if (eq_cstr ("-domsz", arg)) {
      if (!fildesh_parse_unsigned(&domsz_override, argv[argi++]) || domsz_override == 0)
        failout_sysCx("Argument Usage: -domsz <M>\nWhere <M> is a positive integer!");
    }
    else if (eq_cstr ("-cutoff", arg)) {
      if (!fildesh_parse_unsigned(&cutoff, argv[argi++]) || cutoff == 0)
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
    if (in) {
      failout_sysCx ("-domsz only works with -x-list.");
    }
    if (domsz > domsz_override) {
      failout_sysCx ("The given -domsz is not large enough for the given protocol.");
    }
    domsz = domsz_override;
  }

  if (acts.sz() > 0) {
    // Protocol given as a list of actions.
    ppgfun = uniring_ppgfun_of(acts, domsz);
  }
  else {
    if (!in) {
      in = open_FildeshXF("-");
    }
    // Protocol given as an ID.
    domsz = xget_b64_ppgfun(in, ppgfun);
    if (domsz == 0)
      failout_sysCx ("Failed to read protocol.");
    acts = uniring_actions_of(ppgfun);
    close_FildeshX(in);
  }

  if (svg_livelock_ofilename) {
    Table<PcState> top, col;
    if (cutoff == 0) {
      failout_sysCx ("Must provide a -cutoff when using -o-svg-livelock.");
    }
    Trit livelock_exists =
      livelock_semick(cutoff, ppgfun, domsz, &top, &col);

    if (livelock_exists==Yes) {
      fildesh::ofstream svg_out(svg_livelock_ofilename);
      oput_svg_livelock(svg_out, ppgfun, top, col, domsz);
    }
    else {
      DBog0("No livelock detected for given -cutoff.");
    }
  }

  if (prot_ofilename) {
    oput_protocon(prot_ofilename, acts, domsz);
  }

  if (id_ofilename) {
    fildesh::ofstream id_ofile(id_ofilename);
    oput_b64_ppgfun(id_ofile, ppgfun, domsz);
    id_ofile << '\n';
  }

  if (graphviz_ofilename) {
    fildesh::ofstream graphviz_ofile(graphviz_ofilename);
    oput_graphviz(graphviz_ofile, acts);
  }

  if (list_ofilename) {
    fildesh::ofstream list_ofile(list_ofilename);
    oput_list(list_ofile, acts);
  }

  lose_sysCx ();
  return 0;
}

END_NAMESPACE

int main(int argc, char** argv) {
  return PROTOCON_NAMESPACE::main(argc, argv);
}
