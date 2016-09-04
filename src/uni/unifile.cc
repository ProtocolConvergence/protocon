
extern "C" {
#include "cx/syscx.h"
}


#include "cx/fileb.hh"
#include "cx/map.hh"
#include "cx/table.hh"
#include "cx/bittable.hh"

#include "../namespace.hh"


OFile& operator<<(OFile& of, const BitTable& bt)
{
  for (zuint i = 0; i < bt.sz(); ++i)
    of << bt[i];
  return of;
}

static
  bool
xget_triple(C::XFile* xfile, UniAct& act)
{
  C::XFile olay[1];
  if (!getlined_olay_XFile (olay, xfile, "\n"))
    return false;
  uint a, b, c;
  if (xget_uint_XFile (olay, &a)) {
    if (xget_uint_XFile (olay, &b) &&
        xget_uint_XFile (olay, &c)) {
      act = UniAct(a, b, c);
      return true;
    }
    else {
      failout_sysCx("I didn't read a full triple. Malformed input?");
    }
  }
  return false;
}

static
  uint
xget_actions(C::XFile* xfile, Table<UniAct>& acts)
{
  UniAct act;
  while (xget_triple(xfile, act)) {
    acts << act;
  }
  if (acts.sz()==0) {
    failout_sysCx("No actions given! Please provide triples on standard input.");
  }
  uint domsz = 0;
  for (uint i = 0; i < acts.sz(); ++i) {
    for (uint j = 0; j < 3; ++j) {
      if (acts[i][j]+1 > domsz) {
        domsz = acts[i][j]+1;
      }
    }
  }
  return domsz;
}

  void
map_livelock_ppgs(void (*f) (void**, const UniAct&, uint, uint),
                  void** ctx,
                  const Table<PcState>& bot,
                  const Table<PcState>& col,
                  const Table<PcState>& ppgfun,
                  const uint domsz)
{
  const uint n = bot.sz() - 1;
  const uint m = col.sz() - 1;
  Claim( bot[0] == bot[n] );
  Claim( bot[0] == col[m] );
  Claim( bot[0] == col[0] );
  Table<PcState> row;
  row.affysz(n+1);
  for (uint j = 1; j < n+1; ++j) {
    row[j] = bot[j];
  }
  for (uint i = 1; i < m+1; ++i) {
    row[0] = col[i];
    for (uint j = 1; j < n+1; ++j) {
      const PcState a = row[j-1];
      const PcState b = row[j];
      const PcState c = ppgfun[id_of2(a, b, domsz)];
      Claim( c < domsz );
      row[j] = c;
      f(ctx, UniAct(a, b, c), i-1, j-1);
    }
  }
}

  void
oput_uniring_invariant(OFile& ofile, const BitTable& set, const uint domsz,
                       const char* pfx = "", const char* delim = " || ")
{
  UniAct prev( domsz );
  if (!delim)
    delim = pfx;

  Set< Tuple<uint, 2> > cache;
  for each_in_BitTable(actid , set) {
    UniAct act = UniAct::of_id(actid, domsz);
    act[2] = domsz;
    skip_unless (act != prev);
    ofile
      << pfx
      << "!(x[i-1]==" << act[0]
      << " && x[i]==" << act[1] << ")"
      ;
    pfx = delim;
    prev = act;
  }
}

  void
oput_uniring_protocon_file(const String& ofilepath, const String& ofilename,
                           const BitTable& actset, const FilterOpt& opt)
{
  const uint domsz = opt.domsz;
  OFileB ofb;
  OFile ofile( ofb.uopen(ofilepath, ofilename) );

  ofile
    << "// " << actset
    << "\nconstant N := 3;"
    << "\nconstant M := " << domsz << ";"
    << "\nvariable x[N] < M;"
    << "\nprocess P[i < N]"
    << "\n{"
    << "\n  read: x[i-1];"
    << "\n  write: x[i];"
    << "\n  (future & silent)"
    << "\n    (1==1"
    ;
  oput_uniring_invariant(ofile, actset, domsz, "\n     && ", 0);
  ofile << "\n    );";
  ofile << "\n  puppet:";
  for each_in_BitTable(actid , actset) {
    UniAct act = UniAct::of_id(actid, domsz);
    ofile << "\n    "
      << "( x[i-1]==" << act[0]
      << " && x[i]==" << act[1]
      << " --> x[i]:=" << act[2] << "; )";
  }
  ofile << "\n    ;";
  ofile << "\n}\n";
}


static void
oput_graphviz(OFile& ofile, const BitTable& set, uint domsz)
{
  ofile << "digraph G {\n"
    << " margin=0;\n"
    << " edge [weight=5];\n\n";

  for (PcState a = 0; a < domsz; ++a) {
    ofile << "  s_" << a
      << " [label=\"" << a << "\"];\n";
  }

  for each_in_BitTable(actid , set) {
    UniAct act = UniAct::of_id(actid, domsz);

    ofile << "  "
      << "s_" << act[0] << " -> " << "s_" << act[2]
      << "[label=\"" << act[1] << "\"];\n";
  }
  ofile << "}\n";
}

static void
oput_svg_tile(OFile& ofile, const UniAct& act, uint y, uint x, uint d)
{
  const char rect_style[] = " fill=\"none\" stroke=\"black\" stroke-width=\"4\"";
  const char line_style[] = " stroke=\"black\" stroke-width=\"2\"";
  const char text_style[] = " fill=\"black\" font-family=\"Latin Modern, sans\" text-anchor=\"middle\"";
  //" dominant-baseline=\"middle\"";
  const char text_nw_style[] = " font-size=\"24\"";
  const char text_se_style[] = " font-size=\"32\"";
#define LOC(x,p)  (x+p*d/100)
  ofile
    << "\n<rect x=\"" << x << "\" y=\"" << y
    << "\" width=\"" << d << "\" height=\"" << d << "\"" << rect_style << " />"
    << "\n<line x1=\"" << x << "\" y1=\"" << (y+d)
    << "\" x2=\"" << LOC(x,100) << "\" y2=\"" << y << "\"" << line_style << " />"
    << "<line x1=\"" << x << "\" y1=\"" << y
    << "\" x2=\"" << LOC(x,50) << "\" y2=\"" << LOC(y,50) << "\"" << line_style << " />"
    << "\n<text x=\"" << LOC(x,20) << "\" y=\"" << LOC(y,57) << "\""
    << text_style << text_nw_style << ">" << act[0] << "</text>"
    << "\n<text x=\"" << LOC(x,50) << "\" y=\"" << LOC(y,27) << "\""
    << text_style << text_nw_style << ">" << act[1] << "</text>"
    << "\n<text x=\"" << LOC(x,70) << "\" y=\"" << LOC(y,85) << "\""
    << text_style << text_se_style << ">" << act[2] << "</text>"
    ;
#undef LOC
}

static void
oput_svg_tile_callback(void** data, const UniAct& act, uint i, uint j)
{
  const uint d = *(uint*)data[1];
  const uint border = *(uint*)data[2];
  oput_svg_tile(*(OFile*)data[0], act, i*d+border, j*d+border, d);
}


static void
oput_svg_livelock(OFile& ofile, const Table<PcState>& ppgfun,
                  const Table<PcState>& bot,
                  const Table<PcState>& col,
                  const PcState domsz)
{
  const uint n = bot.sz()-1;
  const uint m = col.sz()-1;
  const uint d = 100;
  const uint border = 3;
  ofile << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
    << "\n<!DOCTYPE svg PUBLIC \"-//W3C//DTD SVG 1.1 Basic//EN\""
    << " \"http://www.w3.org/Graphics/SVG/1.1/DTD/svg11-basic.dtd\">"
    << "\n<svg xmlns=\"http://www.w3.org/2000/svg\" xmlns:xlink=\"http://www.w3.org/1999/xlink\""
    << " version=\"1.1\" baseProfile=\"basic\" id=\"svg-root\""
    << " width=\"" << (n*d + 2*border) << "\" height=\"" << (m*d + 2*border) << "\">"
    << "\n<rect x=\"0\" y=\"0\""
    << " width=\""  << (n*d + 2*border) << "\""
    << " height=\"" << (m*d + 2*border) << "\""
    << " fill=\"white\" stroke=\"white\" stroke-width=\"0\" />"
    ;

  {
    uint tmp_d = d;
    uint tmp_border = border;
    void* data[3] = { &ofile, &tmp_d, &tmp_border };
    map_livelock_ppgs(oput_svg_tile_callback, data,
                      bot, col, ppgfun, domsz);
  }

  ofile << "\n</svg>";
}

static bool
xget_BitTable (C::XFile* xfile, BitTable& set)
{
  C::XFile olay[1];
  if (!getlined_olay_XFile (olay, xfile, "\n"))
    return false;
  skipds_XFile (olay, 0);
  set.wipe(0);
  char c;
  for (uint i = 0; i < set.sz(); ++i) {
    if (xget_char_XFile (olay, &c)) {
      if (c != '0' && c != '1') {
        failout_sysCx ("unknown char!");
      }
      if (c == '1')
        set.set1(i);
    }
    else if (i == 0) {
      return false;
    }
    else {
      failout_sysCx ("not enough bits!");
    }
  }
  if (xget_char_XFile (olay, &c)) {
    failout_sysCx ("too many bits!");
  }
  return true;
}

  bool
TestKnownAperiodic()
{
  const uint domsz = 29;
  static const uint AperiodicTileset[][3] = {
    {  0, 13,  8 }, {  0, 14, 10 }, {  0, 15, 12 }, {  0, 16, 12 },
    {  0, 17,  9 }, {  0, 18,  8 }, {  0, 19, 10 }, {  0, 20, 10 },
    {  0, 21, 10 }, {  0, 22,  7 }, {  0, 23, 11 }, {  0, 24, 11 },
    {  0, 25,  7 }, {  0, 26,  7 }, {  0, 27,  9 }, {  0, 28,  9 },
    {  1,  7, 13 }, {  1, 11, 14 },
    {  2,  9, 15 }, {  2, 10, 16 }, {  2, 11, 17 },
    {  3,  8, 18 }, {  3,  9, 19 }, {  3, 10, 20 }, {  3, 12, 21 },
    {  4,  8, 22 }, {  4,  9, 23 }, {  4, 10, 24 },
    {  5,  7, 25 }, {  5,  8, 26 },
    {  6,  9, 27 }, {  6, 12, 28 },
    {  7,  3,  0 }, {  7,  4,  0 }, {  7,  6,  0 },
    {  8,  2,  0 }, {  8,  6,  0 },
    {  9,  1,  0 }, {  9,  3,  0 }, {  9,  4,  0 },
    { 10,  1,  0 }, { 10,  3,  0 }, { 10,  4,  0 }, { 10,  5,  0 },
    { 11,  4,  0 }, { 11,  5,  0 },
    { 12,  1,  0 }, { 12,  2,  0 },
    { 13,  0,  2 },
    { 14,  0,  1 },
    { 15,  0,  2 },
    { 16,  0,  1 },
    { 17,  0,  1 },
    { 18,  0,  6 },
    { 19,  0,  4 },
    { 20,  0,  5 },
    { 21,  0,  3 },
    { 22,  0,  6 },
    { 23,  0,  4 },
    { 24,  0,  5 },
    { 25,  0,  4 },
    { 26,  0,  3 },
    { 27,  0,  4 },
    { 28,  0,  3 }
  };
  const uint depth = ArraySz(AperiodicTileset);

  BitTable delegates( domsz*domsz*domsz, 0 );
  for (uint i = 0; i < ArraySz(AperiodicTileset); ++i) {
    const uint* tile = AperiodicTileset[i];
    delegates.set1(id_of3(tile[0], tile[1], tile[2], domsz));
  }
  return true;
}

END_NAMESPACE
