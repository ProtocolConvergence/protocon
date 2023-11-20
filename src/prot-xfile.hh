
#ifndef ProtoconFile_HH_
#define ProtoconFile_HH_

#include "xnsys.hh"
#include "cx/sesp.h"

#include "cx/synhax.hh"
#include "namespace.hh"

class ProtoconFileOpt
{
public:
  std::string text;
  Map< std::string, Xn::NatMap > constant_map;
  Xn::InvariantStyle invariant_style;
  Xn::InvariantScope invariant_scope;
  Xn::InvariantBehav invariant_behav;

  ProtoconFileOpt()
    : invariant_style( Xn::NInvariantStyles )
    , invariant_scope( Xn::NInvariantScopes )
    , invariant_behav( Xn::NInvariantBehavs )
  {}
};

bool ReadProtoconFile(Xn::Sys& sys, const ProtoconFileOpt& opt);

struct FinMeta
{
  Sesp sp;
  Bit int_ck;
  union {
    int i;
    const char* s;
    Xn::VariableAccessType access_type;
  } aux;
  //uint text_lineno;
};


struct ProtoconFilePcSymm {
  Table<Sesp> shadow_sps;
  Table<Sesp> puppet_sps;
  Table<Sesp> direct_sps;
  Sesp invariant_sp;
  ProtoconFilePcSymm()
    : invariant_sp( 0 )
  {}
};

class ProtoconFile {
private:
  ProtoconFile(const ProtoconFile&);
  ProtoconFile& operator=(const ProtoconFile&);

public:
  bool allgood;
  unsigned text_nlines;
  FildeshX* in_;
  // TODO:
  //Table<ProtoconFilePcSymm> pcsymm_fmlas;

  Map< std::string, int > index_map;
  Map< std::string, const Xn::VblSymm* > vbl_map;
  Map< std::string, Sesp > scope_let_map;
  Xn::Sys* sys;
  Xn::Spec* spec;
  SespCtx* spctx;
  Mem<Xn::PcSymm> pc_symm;
  Mem<Xn::PcSymmSpec> pc_symm_spec;
  Mem<Xn::Pc> pc_in_use;
  X::Fmla permit_xn;
  Table<Xn::ActSymm> conflict;
  bool legit_mode_assigned;

  ProtoconFile(Xn::Sys* sys, FildeshX* in)
    : allgood( true )
    , text_nlines(0)
    , in_(in)
    , pc_symm(0)
    , pc_symm_spec(0)
    , pc_in_use(0)
    , permit_xn(false)
    , legit_mode_assigned(false)
  {
    this->sys = sys;
    this->spec = sys->spec;
    this->sys->invariant = true;
    spctx = make_SespCtx ();
  }

  ~ProtoconFile() {
    free_SespCtx (this->spctx);
  }

  bool interpret_ck() const
  { return !sys->topology.featherweight; }

  bool update_allgood(bool good);
  void bad_parse(const char* text, const char* reason=0);
  bool add_variables(Sesp vbl_name_sp, Sesp vbl_nmembs_sp, Sesp vbl_dom_sp,
                     Xn::ShadowPuppetRole role);

  bool add_processes(Sesp pc_name, Sesp idx_name, Sesp npcs, Sesp map_vbl, Sesp map_expr);

  bool add_constant(Sesp name_sp, Sesp val_sp);

  bool add_constant_list(Sesp name_sp, Sesp list_sp);

  bool add_let(Sesp name_sp, Sesp val_sp);

  bool add_scope_let(Sesp name_sp, Sesp val_sp);

  void del_scope_let(Sesp name_sp);

  bool add_access(Sesp vbl_sp, Xn::VariableAccessType access_type);

  bool add_symmetric_links(Sesp let_names_sp, Sesp let_vals_list_sp);

  bool add_symmetric_access(Sesp let_names_sp, Sesp let_vals_list_sp, Sesp vbls_sp,
                            Xn::VariableAccessType access_type);

  bool parse_action(X::Fmla& act_xn, uint pcidx, Sesp act_sp,
                    bool auto_iden, Xn::ShadowPuppetRole role);
  bool parse_action(X::Fmla& act_pf, Table<X::Fmla>& pc_xns, Sesp act_sp,
                    bool auto_iden, Xn::ShadowPuppetRole role);

  bool add_action(Sesp act_sp, Xn::ShadowPuppetRole role);

  bool forbid_action(Sesp act_sp);
  bool permit_action(Sesp act_sp);
  bool conflict_action(Sesp act_sp);
  bool push_conflict_action();

  bool add_pc_predicate(Sesp name_sp, Sesp val_sp);

  bool add_pc_assume(Sesp assume_sp);

  bool add_pc_legit(Sesp legit_sp);

  bool finish_pc_def();

  bool add_predicate(Sesp name_sp, Sesp val_sp);

  bool add_assume(Sesp assume_sp);
  bool assign_legit_mode(Xn::InvariantStyle style,
                         Xn::InvariantScope scope = Xn::DirectInvariant);
  bool add_legit(Sesp legit_sp);

  bool string_expression(std::string& ss, Sesp a);
  bool parend_string_expression(std::string& ss, Sesp a);

  bool eval(P::Fmla& pf, Sesp a);

  bool eval(IntPFmla& ipf, Sesp a);

  bool eval_int(int* ret, Sesp sp);

  bool eval_nat(uint* ret, Sesp sp);

  bool eval_gtz(uint* ret, Sesp sp);

  bool eval_vbl(IntPFmla* ret, const std::string& name, Sesp idx_sp);

  void within_process(uint pcidx);
  void escape_process();

  bool lookup_vbl(Xn::Vbl** ret, const std::string& name, Sesp c);
  bool lookup_pfmla(P::Fmla* ret, const std::string& name);
  bool lookup_int(int* ret, const std::string& name);
};

END_NAMESPACE
#endif

