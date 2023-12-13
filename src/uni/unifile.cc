
#include "unifile.hh"

#include <map>

#include <fildesh/istream.hh>
#include <fildesh/ostream.hh>
#include <fildesh/string.hh>

#include "src/cx/bittable.hh"
#include "src/cx/table.hh"

#include "src/namespace.hh"

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

  Table<PcState> ppgfun(domsz*domsz, domsz);
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

  Table<PcState> ppgfun(domsz*domsz, domsz);
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

std::ostream& operator<<(std::ostream& of, const BitTable& bt)
{
  for (zuint i = 0; i < bt.sz(); ++i)
    of << bt[i];
  return of;
}

  std::ostream&
oput_b64_ppgfun(std::ostream& ofile, const Table<PcState>& ppgfun, uint domsz)
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
  return ofile;
}

  PcState
xget_b64_ppgfun(FildeshX* in, Table<PcState>& ppgfun)
{
  skipchrs_FildeshX(in, " \t\r\n");
  std::string_view s = fildesh::make_string_view(
      until_char_FildeshX(in, '\n'));
  if (s.empty()) {return 0;}
  const size_t n = s.size();
  size_t domsz = 1;
  unsigned elgsz = 1;
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
  for (size_t i = 0; i < ppgfun.sz(); ++i) {
    const PcState c = bt.get(elgsz*i, elgsz);
    ppgfun[i] = (c < domsz ? c : domsz);
  }
  return (PcState) domsz;
}

  PcState
xget_list(FildeshX* in, Table<UniAct>& acts)
{
  const char* err_msg = NULL;
  UniAct act;
  for (FildeshX slice = until_char_FildeshX(in, '\n');
       slice.at;
       slice = until_char_FildeshX(in, '\n'))
  {
    unsigned a = 0, b = 0, c = 0;
    if (parse_unsigned_FildeshX(&slice, &a)) {
      if (parse_unsigned_FildeshX(&slice, &b) &&
          parse_unsigned_FildeshX(&slice, &c)) {
        acts.push_back(UniAct(a, b, c));
      }
      else {
        err_msg = "I didn't read a full triple. Malformed input?";
        break;
      }
    }
    skip_bytestring_FildeshX(in, NULL, 1);
  }
  if (!err_msg && acts.size() == 0) {
    err_msg = "No actions given! Please provide triples on standard input.";
  }
  if (err_msg) {failout_sysCx(err_msg);}
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
oput_list(std::ostream& ofile, const Table<UniAct>& acts)
{
  for (uint i = 0; i < acts.sz(); ++i) {
    ofile
      << acts[i][0] << '\t'
      << acts[i][1] << '\t'
      << acts[i][2] << '\n';
  }
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
  Table<PcState> row(n+1);
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
oput_uniring_invariant(std::ostream& ofile, const BitTable& set, const uint domsz,
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
oput_protocon(std::ostream& out, const Table<UniAct>& acts, unsigned domsz)
{
  const bool direct_invariant_on = true;
  if (domsz == 0) {
    domsz = uniring_domsz_of(acts);
  }

  out
    << "constant N := 2;"
    << "\nconstant M := " << domsz << ";"
    << "\nvariable x[N] < M;"
    << (direct_invariant_on ? "" : "\n(future & future silent) (true);")
    << "\nprocess P[i < N]"
    << "\n{"
    << "\n  read: x[i-1];"
    << "\n  write: x[i];";
  if (direct_invariant_on) {
    out
      << "\n  (future & silent)"
      << "\n    (true";
    oput_uniring_invariant(
        out,
        uniring_actset_of(uniring_ppgfun_of(acts, domsz), domsz),
        domsz,
        "\n     && ",
        NULL);
    out
      << ");";
  }
  out
    << "\n  puppet:";
  for (uint i = 0; i < acts.sz(); ++i) {
    const UniAct& act = acts[i];
    out << "\n    "
      << "( x[i-1]==" << act[0]
      << " && x[i]==" << act[1]
      << " --> x[i]:=" << act[2] << "; )";
  }
  out
    << "\n    ;"
    << "\n}\n";
}

  void
oput_protocon(const char* ofilename, const Table<UniAct>& acts, uint domsz)
{
  fildesh::ofstream ofile(ofilename);
  oput_protocon(ofile, acts, domsz);
}

  void
oput_promela(std::ostream& ofile, const Table<UniAct>& acts, uint domsz)
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
  ofile << "\n    select(tmp : 0.." << (domsz-1) << ");";
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
oput_graphviz(std::ostream& ofile, const Table<UniAct>& acts)
{
  ofile << "digraph G {"
    << "\n  margin=0;"
    << "\n  edge [weight=5];\n";

  const uint domsz = uniring_domsz_of(acts);
  for (PcState a = 0; a < domsz; ++a) {
    ofile << "\n  " << a
      << " [label=\"" << a << "\"];";
  }

  std::map<UniStep, std::string> edges;
  for (uint i = 0; i < acts.sz(); ++i) {
    std::string& label = edges[UniStep(acts[i][0], acts[i][2])];
    if (!label.empty()) {
      label += '|';
    }
    label += std::to_string(acts[i][1]);
  }

  for (auto it = edges.begin(); it != edges.end(); ++it) {
    const UniStep& edge = it->first;
    const std::string& label = it->second;
    ofile << "\n  "
      << edge[0] << " -> " << edge[1]
      << " [label=\"" << label.c_str() << "\"];";
  }
  ofile << "\n}\n";
}

static void
oput_svg_tile(std::ostream& ofile, const UniAct& act, uint y, uint x, uint d)
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
  oput_svg_tile(*(std::ostream*)data[0], act, i*d+border, j*d+border, d);
}

  void
oput_svg_livelock(std::ostream& ofile, const Table<PcState>& ppgfun,
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

END_NAMESPACE
