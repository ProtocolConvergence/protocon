
#include "udp-ofile.hh"

#include "cx/map.hh"
#include "cx/table.hh"
#include "xnsys.hh"

#include "namespace.hh"

namespace {
struct Variable {
  uint vbl_idx;
  uint domsz;
  bool writing;
};
struct Channel {
  uint pcidx;
  Table<uint> vbls;
};
struct Process {
  Table<Variable> vbls;
  Map<uint,uint> local_idcs;
  Map<uint,uint> chan_map;
  Table<Channel> chans;
};
}

void oput_udp_include_file(std::ostream& ofile, const Xn::Sys& sys, const Xn::Net& o_topology)
{
  const Xn::Net& topo = sys.topology;

  Table<uint> owning(o_topology.vbls.sz());
  Table<Process> pcs(o_topology.pcs.sz());

  for (uint i = 0; i < owning.sz(); ++i) {
    owning[i] = pcs.sz();
  }

  for (uint pcidx = 0; pcidx < pcs.sz(); ++pcidx) {
    const Xn::Pc& pc = o_topology.pcs[pcidx];
    for (uint i = 0; i < pc.rvbls.sz(); ++i) {
      const Xn::Vbl& vbl = *pc.rvbls[i];
      skip_unless (vbl.symm->puppet_ck());
      const uint vidx =  o_topology.vbls.index_of(&vbl);
      Variable v;
      v.vbl_idx = vidx;
      v.domsz = vbl.symm->domsz;
      v.writing = pc.symm->write_ck(i);
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
    }
  }

  // Set up channels for to others.
  for (uint pcidx = 0; pcidx < pcs.sz(); ++pcidx) {
    Process& process = pcs[pcidx];
    for (uint i = 0; i < process.vbls.sz(); ++i) {
      const Variable& v = process.vbls[i];
      uint owning_pcidx = owning[v.vbl_idx];
      if (owning_pcidx == pcidx)  continue;
      uint& o_idx = process.chan_map.ensure(owning_pcidx,
                                            (uint)process.chans.sz());
      if (o_idx == process.chans.sz()) {
        Channel& o_channel = process.chans.grow1();
        o_channel.pcidx = owning_pcidx;
      }
    }
  }

  // Set up channels from others.
  for (uint pcidx = 0; pcidx < pcs.sz(); ++pcidx) {
    Process& process = pcs[pcidx];
    for (uint i = 0; i < process.vbls.sz(); ++i) {
      const Variable& v = process.vbls[i];
      uint owning_pcidx = owning[v.vbl_idx];
      if (owning_pcidx == pcidx)  continue;

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
    << "\n#define Max_NChannels " << max_nchannels
    << "\n#define Max_NVariables " << max_nvbls
    << "\n#define NProcesses " << pcs.sz()
    //////////////////////////////////////////////////////////////////////////
    << "\nuint process_of_channel(PcIden pc, uint channel_idx)"
    << "\n{"
    << "\n#define T(ret)  if (0==channel_idx)  return ret; channel_idx -= 1"
    << "\n  switch (pc.idx) {"
    ;
  for (uint pcidx = 0; pcidx < pcs.sz(); ++pcidx) {
    Process& process = pcs[pcidx];
    ofile << "\n  case " << pcidx << ":";
    for (uint chanidx = 0; chanidx < process.chans.sz(); ++chanidx) {
      ofile << " T( " << process.chans[chanidx].pcidx << " );";
    }
    ofile << " break;";
  }
  ofile
    << "\n  default: break;"
    << "\n  }"
    << "\n  return pc.idx;"
    << "\n#undef T"
    << "\n}"
    //////////////////////////////////////////////////////////////////////////
    << "\nuint variable_of_channel(PcIden pc, uint channel_idx, uint i, Bool writing)"
    << "\n{"
    << "\n  "
    ;
  String prev_str = "";
  for (uint pcidx = 0; pcidx < pcs.sz(); ++pcidx) {
    Process& process = pcs[pcidx];
    String str = "";
    str << "\n    if (writing) {";
    for (uint chanidx = 0; chanidx < process.chans.sz(); ++chanidx) {
      const Channel& o_channel = process.chans[chanidx];
      for (uint i = 0; i < o_channel.vbls.sz(); ++i) {
        str << "\n      if (channel_idx==" << chanidx
          << " && i==" << i
          << ")  return " << process.local_idcs[o_channel.vbls[i]] << ";";
      }
    }
    str << "\n    }\n    else {";
    for (uint chanidx = 0; chanidx < process.chans.sz(); ++chanidx) {
      const Channel& o_channel = process.chans[chanidx];
      const Process& other = pcs[o_channel.pcidx];
      const Channel& x_channel = other.chans[*other.chan_map.lookup(pcidx)];
      for (uint i = 0; i < x_channel.vbls.sz(); ++i) {
        str << "\n      if (channel_idx==" << chanidx
          << " && i==" << i
          << ")  return " << process.local_idcs[x_channel.vbls[i]] << ";";
      }
    }
    str << "\n    }";
    if (str != prev_str) {
      if (!prev_str.empty()) {
        ofile << "if (pc.idx < " << pcidx << ") {" << prev_str << "\n  }\n  else ";
      }
      prev_str = str;
    }
  }
  if (!prev_str.empty()) {
    ofile << "if (pc.idx < " << pcs.sz() << ") {" << prev_str << "\n  }";
  }
  ofile
    << "\n  return Max_NVariables;"
    << "\n}"
    //////////////////////////////////////////////////////////////////////////
    << "\nuint domsz_of_variable(PcIden pc, uint vbl_idx)"
    << "\n{"
    << "\n  if (0) {}"
    ;
  uint symm_cutoff = 0;
  for (uint pc_symm_idx = 0; pc_symm_idx < topo.pc_symms.sz(); ++pc_symm_idx) {
    const Xn::PcSymm& pc_symm = topo.pc_symms[pc_symm_idx];
    if (pc_symm.membs.sz() == 0)  continue;

    symm_cutoff += o_topology.pc_symms[pc_symm_idx].membs.sz();
    ofile << "\n  else if (pc.idx < " << symm_cutoff << ") {";

    uint puppet_i = 0;
    for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
      skip_unless (pc_symm.rvbl_symms[i]->puppet_ck());
      ofile << "\n    if (vbl_idx==" << puppet_i << ")  return "
        << pc_symm.rvbl_symms[i]->domsz
        << ";";
      puppet_i += 1;
    }

    ofile << "\n  }";
  }

  ofile
    << "\n  return 0;"
    << "\n}"
    //////////////////////////////////////////////////////////////////////////
    << "\nvoid assume_assign(PcIden pc, uint8_t* x)"
    << "\n{"
    << "\n  if (0) {"
    ;

  symm_cutoff = 0;
  for (uint pc_symm_idx = 0; pc_symm_idx < topo.pc_symms.sz(); ++pc_symm_idx) {
    const Xn::PcSymm& pc_symm = topo.pc_symms[pc_symm_idx];
    if (pc_symm.membs.sz() == 0)  continue;

    symm_cutoff += o_topology.pc_symms[pc_symm_idx].membs.sz();
    ofile
      << "\n  }"
      << "\n  else if (pc.idx < " << symm_cutoff << ") {"
      ;
    uint rep_pcidx = 0;
    pc_symm.representative(&rep_pcidx);
    const Xn::Pc& pc = *pc_symm.membs[rep_pcidx];

    if (pc.closed_assume.tautology_ck())  continue;

    Table<uint> readable;
    Table<uint> writable;
    Table<uint> pfmla_rvbl_idcs;
    Table<uint> pfmla_wvbl_idcs;

    Table<uint> code_rvbl_idcs;
    Table<uint> code_wvbl_idcs;

    for (uint i = 0, puppet_sz = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
      const Xn::VblSymm& vbl_symm = *pc_symm.rvbl_symms[i];
      skip_unless (vbl_symm.puppet_ck());
      puppet_sz += 1;
      if (pc.closed_assume.equiv_ck(pc.closed_assume.smooth_pre(topo.pfmla_vbl(*pc.rvbls[i]))))
        continue;
      uint puppet_i = puppet_sz - 1;
      if (pc_symm.write_ck(i)) {
        writable << puppet_i;
        pfmla_wvbl_idcs << pc.rvbls[i]->pfmla_idx;
      }
      readable << puppet_i;
      pfmla_rvbl_idcs << pc.rvbls[i]->pfmla_idx;
    }

    Table<uint> pre_state( pfmla_rvbl_idcs.sz() );
    Table<uint> img_state( pfmla_wvbl_idcs.sz() );

    P::Fmla bad_pf = ~pc.closed_assume;
    bad_pf.ensure_ctx(topo.pfmla_ctx);
    {
      P::Fmla img_pf = bad_pf;
      for (uint i = 0; i < pc.rvbls.sz(); ++i) {
        if (pc_symm.write_ck(i))  continue;
        img_pf = img_pf.smooth_pre(topo.pfmla_vbl(*pc.rvbls[i]));
      }
      img_pf = ~img_pf;
      if (!img_pf.sat_ck()) {
        failout_sysCx ("Local (assume & closed) can't fix itself!");
      }
      img_pf.state (+img_state, pfmla_wvbl_idcs);
    }

    const char* ifpfx = "/* */";
    while (bad_pf.sat_ck()) {
      ofile << "\n    " << ifpfx << "if (";
      ifpfx = "else ";

      bad_pf.state (+pre_state, pfmla_rvbl_idcs);
      const P::Fmla pre_pf = topo.pfmla_ctx.pfmla_of_state (+pre_state, pfmla_rvbl_idcs);
      bad_pf -= pre_pf;

      for (uint i = 0; i < pre_state.sz(); ++i) {
        if (i > 0)
          ofile << " && ";
        ofile << "x[" << readable[i] << "]==" << pre_state[i];
      }
      ofile << ") {";


      for (uint i = 0; i < img_state.sz(); ++i) {
        ofile << " x[" << writable[i] << "]=" << img_state[i] << ";";
      }
      ofile << " }";
    }
  }

  ofile
    << "\n  }"
    << "\n}"
    //////////////////////////////////////////////////////////////////////////
    << "\nvoid action_assign(PcIden pc, uint8_t* x)"
    << "\n{"
    << "\n  uint8_t tmp_x[Max_NVariables];"
    << "\n  memcpy(tmp_x, x, sizeof(tmp_x));"
    << "\n  if (0) {}"
    ;

  Table<X::Fmla> rep_xns( topo.pc_symms.sz() );
  rep_xns.wipe (P::Fmla(false));

  symm_cutoff = 0;
  Table<uint> actions( sys.actions );
  for (uint ai = 0; ai < actions.sz(); ++ai) {
    Xn::ActSymm act;
    topo.action(act, actions[ai]);

    uint pc_symm_idx = topo.pc_symms.index_of(act.pc_symm);
    const Xn::PcSymm& pc_symm = topo.pc_symms[pc_symm_idx];
    uint rep_pcidx = 0;
    pc_symm.representative(&rep_pcidx);
    rep_xns[pc_symm_idx] |= topo.represented_xns_of_pc (act, rep_pcidx);
  }

  for (uint pc_symm_idx = 0; pc_symm_idx < topo.pc_symms.sz(); ++pc_symm_idx) {
    const Xn::PcSymm& pc_symm = topo.pc_symms[pc_symm_idx];
    if (pc_symm.membs.sz() == 0)  continue;

    symm_cutoff += o_topology.pc_symms[pc_symm_idx].membs.sz();
    ofile << "\n  else if (pc.idx < " << symm_cutoff << ") {";

    uint rep_pcidx = 0;
    pc_symm.representative(&rep_pcidx);
    const Xn::Pc& pc = *pc_symm.membs[rep_pcidx];

    Table<uint> writable;
    Table<uint> pfmla_rvbl_idcs;
    Table<uint> pfmla_wvbl_idcs;

    for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
      const Xn::VblSymm& vbl_symm = *pc_symm.rvbl_symms[i];
      skip_unless (vbl_symm.puppet_ck());
      if (pc.rvbls[i]->random_ck()) {
        ofile << "\n    x[" << pfmla_rvbl_idcs.sz()
          << "] = RandomMod(" << vbl_symm.domsz << ");";
      }
      if (pc_symm.write_ck(i)) {
        uint puppet_i = pfmla_rvbl_idcs.sz();
        writable << puppet_i;
        pfmla_wvbl_idcs << pc.rvbls[i]->pfmla_idx;
      }
      pfmla_rvbl_idcs << pc.rvbls[i]->pfmla_idx;
    }

    X::Fmla& xn = rep_xns[pc_symm_idx];
    xn.ensure_ctx(topo.pfmla_ctx);

    Table<uint> pre_state( pfmla_rvbl_idcs.sz() );
    Table<uint> img_state( pfmla_wvbl_idcs.sz() );

    ofile << "\n    /* */";
    while (xn.sat_ck()) {
      xn.state (+pre_state, pfmla_rvbl_idcs);
      const P::Fmla pre_pf = topo.pfmla_ctx.pfmla_of_state (+pre_state, pfmla_rvbl_idcs);
      P::Fmla img_pf = xn.img(pre_pf);
      xn -= pre_pf;

      ofile << "if (";
      for (uint i = 0; i < pre_state.sz(); ++i) {
        if (i > 0)
          ofile << " && ";
        ofile << "x[" << i << "]==" << pre_state[i];
      }
      ofile << ")";

      Table<String> choice_statements;
      while (img_pf.sat_ck()) {
        img_pf.state (+img_state, pfmla_wvbl_idcs);
        P::Fmla tmp_pf = topo.pfmla_ctx.pfmla_of_state (+img_state, pfmla_wvbl_idcs);
        img_pf -= tmp_pf;
        if (pre_pf.subseteq_ck(tmp_pf))  continue;

        choice_statements.grow1();
        for (uint i = 0; i < img_state.sz(); ++i) {
          choice_statements.top() << " x[" << writable[i] << "]=" << img_state[i] << ";";
        }
      }

      if (choice_statements.sz() == 0) {
        // Only shadow is changing.
        ofile << " {}";
      }
      else if (choice_statements.sz() == 1) {
        ofile << " {" << choice_statements[0] << " }";
      }
      else {
        ofile << " switch (RandomMod(" << choice_statements.sz() << ")) {";
        for (uint i = 0; i < choice_statements.sz(); ++i) {
          ofile << "\n      case " << i << ":" << choice_statements[i] << " break;";
        }
        ofile << "\n    }";
      }
      ofile << "\n    else ";

    }
    ofile << "{ memcpy(x, tmp_x, sizeof(tmp_x)); }\n  }";
  }
  ofile
    << "\n}"
    //////////////////////////////////////////////////////////////////////////
    << "\nvoid action_assign_hook(PcIden pc, const uint8_t* x_pre, const uint8_t* x_img)"
    << "\n{"
    // TODO: Show value changes.
    << "\n  oput_line(\"ACTING!\");"
    << "\n}"
    << "\n"
    ;
}

void oput_udp_file(std::ostream& ofile, const Xn::Sys& sys, const Xn::Net& o_topology)
{
#include "udp-impl/act.embed.h"
  for (uint i = 0; i < nfiles-1; ++i) {
    ofile.write((char*) files_bytes[i], files_nbytes[i]);
  }

  oput_udp_include_file(ofile, sys, o_topology);

  ofile.write((char*) files_bytes[nfiles-1], files_nbytes[nfiles-1]);
}

END_NAMESPACE

