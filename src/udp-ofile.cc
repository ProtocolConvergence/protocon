
#include "udp-ofile.hh"

#include "cx/table.hh"
#include "cx/map.hh"
#include "xnsys.hh"

namespace {
struct Variable {
  uint vbl_idx;
  uint domsz;
  bool writing;
};
struct Channel {
  uint pcidx;
  Cx::Table<uint> vbls;
};
struct Process {
  Cx::Table<Variable> vbls;
  Cx::Map<uint,uint> local_idcs;
  Cx::Map<uint,uint> chan_map;
  Cx::Table<Channel> chans;
};
}

void oput_udp_file(Cx::OFile& ofile, const Xn::Sys& sys)
{
#include "udp-dep/embed.h"
  for (uint i = 0; i < nfiles-1; ++i) {
    ofile.write((char*) files_bytes[i], files_nbytes[i]);
  }

  const Xn::Net& topo = sys.topology;
  Cx::Table<uint> owning(topo.vbls.sz());
  Cx::Table<Process> pcs(topo.pcs.sz());

  for (uint i = 0; i < owning.sz(); ++i) {
    owning[i] = pcs.sz();
  }

  for (uint pcidx = 0; pcidx < pcs.sz(); ++pcidx) {
    const Xn::Pc& pc = topo.pcs[pcidx];
    for (uint i = 0; i < pc.rvbls.sz(); ++i) {
      const Xn::Vbl& vbl = *pc.rvbls[i];
      if (vbl.symm->pure_shadow_ck())  continue;
      const uint vidx =  topo.vbls.index_of(&vbl);
      Variable v;
      v.vbl_idx = vidx;
      v.domsz = vbl.symm->domsz;
      v.writing = pc.symm->write_flags[i];
      pcs[pcidx].local_idcs[vidx] = pcs[pcidx].vbls.sz();
      pcs[pcidx].vbls.push(v);

      if (v.writing && owning[vidx] == pcs.sz()) {
        owning[vidx] = pcidx;
      }
    }
  }

  for (uint pcidx = 0; pcidx < pcs.sz(); ++pcidx) {
    Process& process = pcs[pcidx];
    for (uint i = 0; i < process.vbls.sz(); ++i) {
      const Variable& v = process.vbls[i];
      uint& owning_pcidx = owning[v.vbl_idx];
      if (owning_pcidx == pcs.sz()) {
        owning_pcidx = pcidx;
      }

      if (owning_pcidx != pcidx) {
        uint& o_idx = process.chan_map.ensure(owning_pcidx,
                                              (uint)process.chans.sz());
        if (o_idx == process.chans.sz()) {
          Channel& o_channel = process.chans.grow1();
          o_channel.pcidx = owning_pcidx;
        }

        Process& other = pcs[owning_pcidx];
        uint& x_idx = other.chan_map.ensure(pcidx,
                                            (uint)other.chans.sz());
        if (x_idx == other.chans.sz()) {
          other.chans.grow1();
        }
        Channel& x_channel = other.chans[x_idx];
        x_channel.pcidx = pcidx;
        x_channel.vbls.push(v.vbl_idx);

      }
    }
  }

  uint max_nchannels = 0;
  uint max_nvbls = 0;
  for (uint pcidx = 0; pcidx < pcs.sz(); ++pcidx) {
    if (pcs[pcidx].chans.sz() > max_nchannels) {
      max_nchannels = pcs[pcidx].chans.sz();
    }
    if (pcs[pcidx].vbls.sz() > max_nvbls) {
      max_nvbls = pcs[pcidx].vbls.sz();
    }
  }

  ofile
    << "\n#undef Max_NChannels"
    << "\n#define Max_NChannels " << max_nchannels
    << "\n#undef Max_NVariables"
    << "\n#define Max_NVariables " << max_nvbls
    << "\n#define NProcesses " << pcs.sz()

    << "\nuint process_of_channel(PcIden pc, uint channel_idx)"
    << "\n{"
    << "\n#define L(pcidx, chanidx, ret)\\"
    << "\n  if (pc.idx==pcidx && channel_idx==chanidx)  return ret"
    ;
  for (uint pcidx = 0; pcidx < pcs.sz(); ++pcidx) {
    Process& process = pcs[pcidx];
    for (uint chanidx = 0; chanidx < process.chans.sz(); ++chanidx) {
      ofile << "\nL(" << pcidx << "," << chanidx << ","
        << process.chans[chanidx].pcidx << ");";
    }
  }
  ofile
    << "\n  return pc.idx;"
    << "\n#undef L"
    << "\n}"

    << "\nuint variable_of_channel(PcIden pc, uint channel_idx, uint i, Bool writing)"
    << "\n{"
    << "\n#define W(pcidx, chanidx, access_idx, ret)\\"
    << "\n  if (pc.idx==pcidx && writing && channel_idx==chanidx && i==access_idx)\\"
    << "\n    return ret"
    << "\n#define R(pcidx, chanidx, access_idx, ret)\\"
    << "\n  if (pc.idx==pcidx && !writing && channel_idx==chanidx && i==access_idx)\\"
    << "\n    return ret"
    ;
  for (uint pcidx = 0; pcidx < pcs.sz(); ++pcidx) {
    Process& process = pcs[pcidx];
    for (uint chanidx = 0; chanidx < process.chans.sz(); ++chanidx) {
      const Channel& o_channel = process.chans[chanidx];
      const Process& other = pcs[o_channel.pcidx];
      const Channel& x_channel = other.chans[*other.chan_map.lookup(pcidx)];
      for (uint i = 0; i < o_channel.vbls.sz(); ++i) {
        ofile << "\nW(" << pcidx << "," << chanidx << "," << i << ","
          << process.local_idcs[o_channel.vbls[i]] << ");";
      }
      for (uint i = 0; i < x_channel.vbls.sz(); ++i) {
        ofile << "\nR(" << pcidx << "," << chanidx << "," << i << ","
          << process.local_idcs[x_channel.vbls[i]] << ");";
      }
    }
  }
  ofile
    << "\n  return Max_NVariables;"
    << "\n#undef W"
    << "\n#undef R"
    << "\n}"

    << "\nuint domsz_of_variable(PcIden pc, uint vbl_idx)"
    << "\n{"
    << "\n#define L(pcidx, vidx, ret)\\"
    << "\n  if (pc.idx==pcidx && vbl_idx==vidx)\\"
    << "\n    return ret"
    ;
  for (uint pcidx = 0; pcidx < pcs.sz(); ++pcidx) {
    Process& process = pcs[pcidx];
    for (uint i = 0; i < process.vbls.sz(); ++i) {
      ofile << "\nL(" << pcidx << "," << i << ","
        << process.vbls[i].domsz << ");";
    }
  }
  ofile
    << "\n  return 0;"
    << "\n#undef L"
    << "\n}"
    << "\nvoid action_assign(PcIden pc, uint8_t* x)"
    << "\n{"
    ;
  uint symm_cutoff = 0;
  for (uint pc_symm_idx = 0; pc_symm_idx < topo.pc_symms.sz(); ++pc_symm_idx) {
    const Xn::PcSymm& pc_symm = topo.pc_symms[pc_symm_idx];
    symm_cutoff += pc_symm.membs.sz();
    ofile << "\n  " << (pc_symm_idx == 0 ? "" : "else ") << "if (pc.idx < "
      << symm_cutoff << ") {";

    for (uint ai = 0; ai < sys.actions.size(); ++ai) {
      Xn::ActSymm act;
      topo.action(act, sys.actions[ai]);
      if (act.pc_symm != &pc_symm) {
        continue;
      }

      uint puppet_i = 0;
      Cx::Table<uint> writable;
      ofile << "\n    if (";
      for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
        if (pc_symm.rvbl_symms[i]->pure_shadow_ck()) {
          continue;
        }
        if (pc_symm.write_flags[i]) {
          writable.push(puppet_i);
        }

        if (puppet_i > 0) {
          ofile << " && ";
        }
        ofile << "x[" << puppet_i << "]==" << act.guard(i);
        puppet_i += 1;
      }

      ofile << ") { ";
      puppet_i = 0;
      for (uint i = 0; i < pc_symm.wvbl_symms.sz(); ++i) {
        if (pc_symm.wvbl_symms[i]->pure_shadow_ck()) {
          continue;
        }
        ofile << "x[" << writable[puppet_i] << "]=" << act.assign(i) << "; ";
        puppet_i += 1;
      }
      ofile << "}";
    }
    ofile << "\n  }";
  }
  ofile
    << "\n}"
    << "\nvoid action_pre_assign(PcIden pc, const uint8_t* x)"
    << "\n{"
    << "\n  oput_line(\"ACTING!\");"
    << "\n}"
    << "\n"
    ;

  ofile.write((char*) files_bytes[nfiles-1], files_nbytes[nfiles-1]);
}

