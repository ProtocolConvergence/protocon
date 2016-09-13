
extern "C" {
#include "cx/syscx.h"
}

#include "unifile.hh"

#include "cx/bittable.hh"
#include "cx/fileb.hh"
#include "cx/map.hh"
#include "cx/table.hh"

#include "../namespace.hh"

  PcState
uniring_domsz_of(const Table<PcState>& ppgfun)
{
  uint domsz = 0;
  while (domsz * domsz < ppgfun.sz()) {
    domsz += 1;
  }
  if (ppgfun.sz() != domsz * domsz) {
    return 0;
  }
  return domsz;
}

  PcState
uniring_domsz_of(const Table<UniAct>& acts)
{
  uint domsz = 0;
  for (uint i = 0; i < acts.sz(); ++i) {
    for (uint j = 0; j < 3; ++j) {
      if (acts[i][j]+1u > domsz) {
        domsz = acts[i][j]+1;
      }
    }
  }
  return domsz;
}

  PcState
uniring_domsz_of(const BitTable& actset)
{
  uint domsz = 0;
  while (domsz * domsz * domsz < actset.sz()) {
    domsz += 1;
  }
  if (actset.sz() != domsz * domsz * domsz) {
    return 0;
  }
  return domsz;
}

  Table<PcState>
uniring_ppgfun_of(const Table<UniAct>& acts, uint domsz)
{
  if (domsz == 0)
    domsz = uniring_domsz_of(acts);

  Table<PcState> ppgfun;
  ppgfun.affysz(domsz*domsz, domsz);
  for (uint i = 0; i < acts.sz(); ++i) {
    const UniAct& act = acts[i];
    ppgfun[id_of2(act[0], act[1], domsz)] = act[2];
  }
  return ppgfun;
}

  Table<PcState>
uniring_ppgfun_of(const BitTable& actset, uint domsz)
{
  if (domsz == 0)
    domsz = uniring_domsz_of(actset);

  Table<PcState> ppgfun;
  ppgfun.affysz(domsz*domsz, domsz);
  for (zuint i = actset.begidx(); i < actset.sz(); actset.nextidx(&i)) {
    const UniAct& act = UniAct::of_id(i, domsz);
    ppgfun[id_of2(act[0], act[1], domsz)] = act[2];
  }
  return ppgfun;
}


  Table<UniAct>
uniring_actions_of(const Table<PcState>& ppgfun, uint domsz)
{
  if (domsz == 0)
    domsz = uniring_domsz_of(ppgfun);
  Table<UniAct> acts;
  for (uint a = 0; a < domsz; ++a) {
    for (uint b = 0; b < domsz; ++b) {
      uint c = ppgfun[id_of2(a, b, domsz)];
      if (c < domsz) {
        acts << UniAct(a, b, c);
      }
    }
  }
  return acts;
}

  Table<UniAct>
uniring_actions_of(const BitTable& actset, uint domsz)
{
  if (domsz == 0)
    domsz = uniring_domsz_of(actset);
  Claim( domsz != 0 );
  Table<UniAct> acts;
  for (zuint id = actset.begidx(); id < actset.sz(); actset.nextidx(&id)) {
    acts << UniAct::of_id(id, domsz);
  }
  return acts;
}

  BitTable
uniring_actset_of(const Table<PcState>& ppgfun, uint domsz)
{
  if (domsz == 0)
    domsz = uniring_domsz_of(ppgfun);
  BitTable actset(domsz*domsz*domsz, 0);
  for (uint a = 0; a < domsz; ++a) {
    for (uint b = 0; b < domsz; ++b) {
      uint c = ppgfun[id_of2(a, b, domsz)];
      if (c < domsz) {
        actset.set1(id_of3(a, b, c, domsz));
      }
    }
  }
  return actset;
}

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

  void
oput_b64_ppgfun(OFile& ofile, const Table<PcState>& ppgfun, uint domsz)
{
  if (domsz == 0)
    domsz = uniring_domsz_of(ppgfun);
  Claim( domsz > 0 );
  const uint elgsz = 1+lg_luint(domsz);
  // Initialize bitstring with ones.
  // It is 5 longer than necessary so we fill out the 1 bits.
  const uint btsz = domsz * domsz * elgsz;
  BitTable bt(btsz + 5, 1);
  for (zuint i = 0; i < ppgfun.sz(); ++i) {
    const PcState c = ppgfun[i];
    skip_unless (c < domsz);
    bt.set(i * elgsz, elgsz, c);
  }

  for (zuint i = 0; i < btsz; i+=6) {
    const uint w = bt.get(i, 6);
    const char c
      = w < 26 ? 'A'+(char)w
      : w < 52 ? 'a'+(char)(w-26)
      : w < 62 ? '0'+(char)(w-52)
      : w < 63 ? '-' : '_';
    ofile << c;
  }
}

  PcState
xget_b64_ppgfun(C::XFile* xfile, Table<PcState>& ppgfun)
{
  const char* s = nextok_XFile(xfile, 0, 0);
  if (!s)  return 0;
  const zuint n = strlen(s);
  zuint domsz = 1;
  uint elgsz = 1;
  while (domsz * domsz * elgsz + 5 < 6 * n) {
    domsz += 1;
    elgsz = 1+lg_luint(domsz);
  }
  if ((domsz * domsz * elgsz + 5) / 6 != n) {
    DBog2("B64 encoding has %zu bits, which is not close to %s.",
          6*n, "a valid length (domsz^2*lg(domsz+1))");
    return 0;
  }
  BitTable bt(domsz*domsz*elgsz, 0);
  for (zuint i = 0; i < n; ++i) {
    const char c = s[i];
    const uint w
      = ('A' <= c && c <= 'Z') ? (uint) (c-'A')
      : ('a' <= c && c <= 'z') ? (uint) (c-'a') + 26
      : ('0' <= c && c <= '9') ? (uint) (c-'0') + 52
      : ('-' == c) ? 62
      : ('_' == c) ? 63
      : 64;
    if (w >= 64) {
      DBog1( "Error reading B64 encoding, get char '%c'.", c );
      return 0;
    }
    bt.set(6*i, 6, w);
  }

  ppgfun.resize(domsz*domsz);
  for (zuint i = 0; i < ppgfun.sz(); ++i) {
    const PcState c = bt.get(elgsz*i, elgsz);
    ppgfun[i] = (c < domsz ? c : domsz);
  }
  return (PcState) domsz;
}

  PcState
xget_list(C::XFile* xfile, Table<UniAct>& acts)
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
      if (acts[i][j]+1u > domsz) {
        domsz = acts[i][j]+1;
      }
    }
  }
  return domsz;
}

  void
oput_list(OFile& ofile, const Table<UniAct>& acts)
{
  for (uint i = 0; i < acts.sz(); ++i) {
    ofile
      << acts[i][0] << '\t'
      << acts[i][1] << '\t'
      << acts[i][2] << '\n';
  }
}

  PcState
xget_actions(C::XFile* xfile, BitTable& actset)
{
  const char* line = getline_XFile(xfile);
  if (!line)
    return 0;

  actset.resize(strlen(line));
  actset.wipe(0);

  UniAct act;
  for (uint i = 0; i < actset.size(); ++i) {
    if (line[i] == '1') {
      actset.set1(i);
    }
    else if (line[i] != '0') {
      failout_sysCx("Only ones and zeros please.");
    }
  }

  const uint domsz = uniring_domsz_of(actset);
  if (domsz == 0) {
    failout_sysCx("Incorrect bitstring size!");
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
                       const char* pfx, const char* delim)
{
  UniAct prev( domsz );
  if (!delim)
    delim = pfx;

  for (zuint id = set.begidx(); id < set.sz(); set.nextidx(&id)) {
    UniAct act = UniAct::of_id(id, domsz);
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
oput_protocon(OFile& ofile, const Table<UniAct>& acts, uint domsz)
{
  if (domsz == 0) {
    domsz = uniring_domsz_of(acts);
  }

  ofile
    << "constant N := 2;"
    << "\nconstant M := " << domsz << ";"
    << "\nvariable x[N] < M;"
    << "\n(future & future silent) (true);"
    << "\nprocess P[i < N]"
    << "\n{"
    << "\n  read: x[i-1];"
    << "\n  write: x[i];"
    ;
  ofile << "\n  puppet:";
  for (uint i = 0; i < acts.sz(); ++i) {
    const UniAct& act = acts[i];
    ofile << "\n    "
      << "( x[i-1]==" << act[0]
      << " && x[i]==" << act[1]
      << " --> x[i]:=" << act[2] << "; )";
  }
  ofile << "\n    ;";
  ofile << "\n}\n";
}

  void
oput_protocon(const String& ofilename, const Table<UniAct>& acts, uint domsz)
{
  OFileB ofb;
  OFile ofile( ofb.uopen(0, ofilename) );
  oput_protocon(ofile, acts, domsz);
}

  void
oput_promela(OFile& ofile, const Table<UniAct>& acts, uint domsz)
{
  ofile
    << "\n#define N 4"
    << "\nbyte x[N];"
    << "\nbyte initializing = N;"
    << "\n#define x_p x[(_pid+N-1)%N]"
    << "\n#define x_i x[_pid]"
    << "\n#define UniAct(a,b,c)  atomic { (x_p == a) && (x_i == b) -> x_i = c; }"
    << "\nactive[N] proctype P()"
    << "\n{"
    << "\n  atomic {"
    << "\n    if"
    ;
  for (uint i = 0; i < domsz; ++i) {
    ofile << "\n    :: x_i = " << i << ';';
  }
  ofile.printf("\n    select(tmp : 0..%u);", domsz-1);
  ofile
    << "\n    fi;"
    << "\n    initializing --;"
    << "\n  }"
    << "\n  (initializing==0);"
    << "\nend_P:"
    << "\n  do"
    ;

  for (uint i = 0; i < acts.sz(); ++i) {
    ofile << "\n  :: UniAct( "
      << acts[i][0] << ", "
      << acts[i][1] << ", "
      << acts[i][2] << " )";
  }
  ofile
    << "\n  od;"
    << "\n}\n"
    ;
}

  void
oput_graphviz(OFile& ofile, const Table<UniAct>& acts)
{
  ofile << "digraph G {"
    << "\n  margin=0;"
    << "\n  edge [weight=5];\n";

  const uint domsz = uniring_domsz_of(acts);
  for (PcState a = 0; a < domsz; ++a) {
    ofile << "\n  " << a
      << " [label=\"" << a << "\"];";
  }

  Map<UniStep,String> edges;
  for (uint i = 0; i < acts.sz(); ++i) {
    edges[UniStep(acts[i][0], acts[i][2])].push_delim("|") << acts[i][1];
  }

  Map<UniStep, String>::const_iterator it;
  for (it = edges.begin(); it != edges.end(); ++it) {
    const UniStep& edge = it->first;
    const String& label = it->second;
    ofile << "\n  "
      << edge[0] << " -> " << edge[1]
      << " [label=\"" << label.ccstr() << "\"];";
  }
  ofile << "\n}\n";
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

  void
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

  PcState
tilings_and_patterns_aperiodic_uniring(Table<UniAct>& acts)
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
  acts.affysz(ArraySz(AperiodicTileset));
  for (uint i = 0; i < ArraySz(AperiodicTileset); ++i) {
    const uint* tile = AperiodicTileset[i];
    acts[i] = UniAct(tile[0], tile[1], tile[2]);
  }
  return domsz;
}

END_NAMESPACE
