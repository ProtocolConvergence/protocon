

#ifndef XnSys_HH_
#define XnSys_HH_

#include "cx/synhax.hh"
#include "cx/lgtable.hh"
#include "xnpc.hh"

#include "namespace.hh"
namespace Xn {
class Net;
class Sys;
class ManySys;


class Net {
public:
  Mem<Spec> spec;
  PFmlaCtx pfmla_ctx;
  X::FmlaeCtx xfmlae_ctx;
  LgTable< Vbl > vbls;
  LgTable< VblSymm > vbl_symms;
  LgTable< Pc > pcs;
  LgTable< PcSymm > pc_symms;

private:
  Table< X::Fmlae > act_xfmlaes;
public:
  Table< Table<uint> > represented_actions;
  uint n_possible_acts;
  uint total_pre_domsz;
  bool lightweight;
  bool featherweight;
  X::Fmla identity_xn;

  bool random_read_exists;
  bool random_write_exists;
  bool pure_shadow_vbl_exists;
  bool pure_puppet_vbl_exists;

private:
  uint shadow_pfmla_list_id;
  uint puppet_pfmla_list_id;
  uint pure_shadow_pfmla_list_id;
  uint pure_puppet_pfmla_list_id;

public:
  Net()
    : spec(0)
    , pfmla_ctx()
    , xfmlae_ctx(pfmla_ctx)
    , n_possible_acts(0)
    , total_pre_domsz(0)
    , lightweight(false)
    , featherweight(false)
    , identity_xn(true)
    , random_read_exists(false)
    , random_write_exists(false)
    , pure_shadow_vbl_exists(false)
    , pure_puppet_vbl_exists(false)
  {
    this->shadow_pfmla_list_id = this->pfmla_ctx.add_vbl_list();
    this->puppet_pfmla_list_id = this->pfmla_ctx.add_vbl_list();
    this->pure_shadow_pfmla_list_id = this->pfmla_ctx.add_vbl_list();
    this->pure_puppet_pfmla_list_id = this->pfmla_ctx.add_vbl_list();
  }

  void commit_initialization();
  void fixup_pc_xns();

  VblSymm*
  add_variables(const std::string& name, uint nmembs, uint domsz,
                Xn::ShadowPuppetRole role = Xn::Direct);
private:
  void commit_variable(VblSymm& symm, uint i);
public:
  void commit_variables();
  PcSymm*
  add_processes(const std::string& name, const std::string& idx_name, uint nmembs);
  void add_access (PcSymm* pc_symm, const VblSymm* vbl_symm,
                   const NatMap& indices,
                   Xn::VariableAccessType access_type);

  uint action_pcsymm_index(uint actidx) const;
  ActSymm act_of(uint actidx) const;

  void action(ActSymm& act, uint actid) const { act = act_of(actid); }
  uint action_index(const ActSymm& act) const { return id_of(act); }

  uint action_pre_index(uint actidx) const;
  uint action_img_index(uint actidx) const;

  uint representative_action_index(uint actidx) const;

  const X::Fmla action_pfmla(uint actidx) const;
  const X::Fmlae action_xfmlae(uint actidx) const;

  PFmlaVbl pfmla_vbl(uint i) const {
    return this->pfmla_ctx.vbl(this->vbls[i].pfmla_idx);
  }
  PFmlaVbl pfmla_vbl(const Vbl& x) const {
    return this->pfmla_ctx.vbl(x.pfmla_idx);
  }

  PFmlaVbl pfv(uint pc_symm_idx, uint pc_idx, uint vbl_idx) const {
    const Xn::Vbl& vbl = *pc_symms[pc_symm_idx].membs[pc_idx]->rvbls[vbl_idx];
    return pfmla_ctx.vbl(vbl.pfmla_idx);
  }

  bool probabilistic_ck() const {
    return (random_read_exists || random_write_exists);
  }
  bool pure_shadow_vbl_ck() const {
    return pure_shadow_vbl_exists;
  }

  bool safe_ck(const Xn::ActSymm& act) const;

  Cx::PFmla smooth_pure_shadow_vbls(const Cx::PFmla& pf) const {
    if (!pure_shadow_vbl_exists) {
      return pf;
    }
    return pf.smooth(pure_shadow_pfmla_list_id);
  }
  Cx::PFmla smooth_shadow_vbls(const Cx::PFmla& pf) const {
    return pf.smooth(shadow_pfmla_list_id);
  }

  Cx::PFmla smooth_puppet_vbls(const Cx::PFmla& pf) const {
    return pf.smooth(puppet_pfmla_list_id);
  }

  Cx::PFmla smooth_pure_puppet_vbls(const Cx::PFmla& pf) const {
    if (!pure_puppet_vbl_exists) {
      return pf;
    }
    return pf.smooth(pure_puppet_pfmla_list_id);
  }
  Cx::PFmla smooth_pure_puppet_img_vbls(const Cx::PFmla& pf) const {
    if (!pure_puppet_vbl_exists) {
      return pf;
    }
    return pf.smooth_img(pure_puppet_pfmla_list_id);
  }

  Cx::PFmla proj_shadow(const Cx::PFmla& pf) const {
    return this->smooth_pure_puppet_vbls(pf);
  }
  Cx::PFmla proj_img_shadow(const Cx::PFmla& pf) const {
    return this->smooth_pure_puppet_img_vbls(pf);
  }
  Cx::PFmla proj_puppet(const Cx::PFmla& pf) const {
    return this->smooth_pure_shadow_vbls(pf);
  }

  std::ostream& oput(std::ostream& of,
                const Cx::PFmla& pf,
                const std::string& pfx,
                const std::string& sfx) const;

  std::ostream& oput_vbl_names(std::ostream& ofile) const;
  std::ostream& oput_pfmla(std::ostream& ofile, Cx::PFmla pf,
                    Sign pre_or_img, bool just_one) const;
  std::ostream& oput_one_xn(std::ostream& ofile, const X::Fmla& pf) const;
  std::ostream& oput_all_xn(std::ostream& ofile, const X::Fmla& pf) const;
  std::ostream& oput_one_pf(std::ostream& ofile, const P::Fmla& pf) const;
  std::ostream& oput_all_pf(std::ostream& ofile, const P::Fmla& pf) const;


  X::Fmla sync_xn(const Table<uint>& actidcs, const bool fully_synchronous) const;
  X::Fmla semisync_xn(const Table<uint>& actidcs) const;
  X::Fmla xn_of_pc(const Xn::ActSymm& act, uint pcidx) const;
  X::Fmla represented_xns_of_pc(const Xn::ActSymm& act, uint relative_pcidx) const;
  void unroll_action(Table<Xn::ActSymm>& dst, uint actid, bool include_shadow=false) const;

  void make_action_pfmla(X::Fmla* ret_xn, uint actid) const;
  void make_action_xfmlae(X::Fmlae* ret_xn, uint actidx) const;
private:
  void cache_action_xfmla(uint actid);
};

/** This holds the search problem and its solution.**/
class Sys {
public:
  Xn::Net topology;
  Xn::Spec spec[1];
  vector<uint> actions; ///< Force use of these actions.

  PredicateMap predicate_map;

  /// Assumed state predicate, which must remain closed.
  P::Fmla closed_assume;
  /// Invariant to which we should converge.
  P::Fmla invariant;
  bool shadow_puppet_synthesis;
  X::Fmla shadow_pfmla;
  /// Transition relation within the invariant.
  X::Fmla direct_pfmla;
  /// Self-loops in the invariant.
  X::Fmla shadow_self;

private:
  Map<uint,uint> niceIdcs; ///< Niceness for process symmetries, used in search.

public:
  Sys()
    : closed_assume( true )
    , invariant( true )
    , shadow_puppet_synthesis(false)
    , shadow_pfmla(false)
    , direct_pfmla(false)
  {
    topology.spec = spec;
  }

  void commit_initialization();

  bool integrityCk() const;

  /// Do the shadow puppet synthesis
  bool shadow_puppet_synthesis_ck() const {
    return this->shadow_puppet_synthesis;
  }

  void niceIdxFo(uint pcIdx, uint niceIdx) {
    niceIdcs[pcIdx] = niceIdx;
  }
  uint niceIdxOf(uint pcIdx) const {
    const uint* niceIdx = niceIdcs.lookup(pcIdx);
    if (!niceIdx) {
      return topology.pcs.sz() + pcIdx;
    }
    return *niceIdx;
  }
};

class ManySys : public LgTable<Sys>
{
public:
  ManySys() {}
};
}

std::ostream&
OPut(std::ostream& of, const Xn::ActSymm& act);
void
find_one_cycle(Table<P::Fmla>& states,
               const X::Fmla& xn, const P::Fmla& scc,
               const P::Fmla& initial);
void
find_one_cycle(Table<P::Fmla>& states,
               const X::Fmla& xn, const P::Fmla& scc);
void
find_livelock_actions(Table<uint>& actions, const X::Fmla& xn,
                      const P::Fmla& scc, const P::Fmla& invariant,
                      const Xn::Net& topo);
void
oput_one_cycle(std::ostream& of, const X::Fmla& xn,
               const P::Fmla& scc, const P::Fmla& initial,
               const Xn::Net& topo);
bool
candidate_actions(std::vector<uint>& candidates,
                  Table<uint>& dels,
                  Table<uint>& rejs,
                  const Xn::Sys& sys);

END_NAMESPACE
#endif

