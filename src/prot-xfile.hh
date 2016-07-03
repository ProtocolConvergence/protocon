
#ifndef ProtoconFile_HH_
#define ProtoconFile_HH_

#include "cx/synhax.hh"
extern "C" {
#include "cx/sesp.h"
#include "cx/xfile.h"
}
#include "xnsys.hh"

#include "namespace.hh"

class ProtoconFileOpt
{
public:
  String text;
  Map< String, Xn::NatMap > constant_map;
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
  uint text_nlines;
  ::XFile xf;
  // TODO:
  //Table<ProtoconFilePcSymm> pcsymm_fmlas;

  Map< String, int > index_map;
  Map< String, const Xn::VblSymm* > vbl_map;
  Map< String, Sesp > scope_let_map;
  Xn::Sys* sys;
  Xn::Spec* spec;
  SespCtx* spctx;
  Mem<Xn::PcSymm> pc_symm;
  Mem<Xn::PcSymmSpec> pc_symm_spec;
  Mem<Xn::Pc> pc_in_use;
  X::Fmla permit_xn;
  Table<Xn::ActSymm> conflict;
  bool legit_mode_assigned;

  ProtoconFile(Xn::Sys* sys, ::XFile* xf)
    : allgood( true )
    , text_nlines(0)
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
    xget_XFile (xf);
    xf->off = xf->buf.sz-1;
    olay_txt_XFile (&this->xf, xf, 0);
  }

  ~ProtoconFile() {
    free_SespCtx (this->spctx);
  }

  bool interpret_ck() const
  { return !sys->topology.featherweight; }

  bool update_allgood(bool good);
  void bad_parse(const char* text, const char* reason=0);
  bool add_variables(Sesp vbl_name_sp, Sesp vbl_nmembs_sp, Sesp vbl_dom_sp,
                     Xn::Vbl::ShadowPuppetRole role);

  bool add_processes(Sesp pc_name, Sesp idx_name, Sesp npcs, Sesp idx_offset);

  bool add_constant(Sesp name_sp, Sesp val_sp);

  bool add_constant_list(Sesp name_sp, Sesp list_sp);

  bool add_let(Sesp name_sp, Sesp val_sp);

  bool add_scope_let(Sesp name_sp, Sesp val_sp);

  void del_scope_let(Sesp name_sp);

  bool add_access(Sesp vbl_sp, Bit write, Bit random);

  bool add_symmetric_links(Sesp let_names_sp, Sesp let_vals_list_sp);

  bool add_symmetric_access(Sesp let_names_sp, Sesp let_vals_list_sp, Sesp vbls_sp,
                            Bit write, Bit random);

  bool parse_action(X::Fmla& act_xn, uint pcidx, Sesp act_sp,
                    bool auto_iden, Xn::Vbl::ShadowPuppetRole role);
  bool parse_action(X::Fmla& act_pf, Table<X::Fmla>& pc_xns, Sesp act_sp,
                    bool auto_iden, Xn::Vbl::ShadowPuppetRole role);

  bool add_action(Sesp act_sp, Xn::Vbl::ShadowPuppetRole role);

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

  bool string_expression(String& ss, Sesp a);
  bool parend_string_expression(String& ss, Sesp a);

  bool eval(P::Fmla& pf, Sesp a);

  bool eval(IntPFmla& ipf, Sesp a);

  bool eval_int(int* ret, Sesp sp);

  bool eval_nat(uint* ret, Sesp sp);

  bool eval_gtz(uint* ret, Sesp sp);

  bool eval_vbl(IntPFmla* ret, const String& name, Sesp idx_sp);

  void within_process(uint pcidx);
  void escape_process();

  bool lookup_vbl(Xn::Vbl** ret, const String& name, Sesp c);
  bool lookup_pfmla(P::Fmla* ret, const String& name);
  bool lookup_int(int* ret, const String& name);
};

END_NAMESPACE
#endif

