
#ifndef ProtoconFile_HH_
#define ProtoconFile_HH_

#include "cx/synhax.hh"
extern "C" {
#include "cx/sesp.h"
#include "cx/xfile.h"
}
#include "xnsys.hh"

class ProtoconFileOpt
{
public:
  Cx::String file_path;
  Map< Cx::String, uint > constant_map;

  ProtoconFileOpt()
  {}
};

bool ReadProtoconFile(Xn::Sys& sys, const ProtoconFileOpt& opt);

struct FinMeta
{
  Sesp sp;
  Bit int_ck;
  //uint text_lineno;
};


struct ProtoconFilePcSymm {
  Cx::Table<Sesp> shadow_sps;
  Cx::Table<Sesp> puppet_sps;
  Cx::Table<Sesp> direct_sps;
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
  XFile xf;
  // TODO:
  //Cx::Table<ProtoconFilePcSymm> pcsymm_fmlas;

  Map< Cx::String, int > index_map;
  Map< Cx::String, const Xn::VblSymm* > vbl_map;
  Map< Cx::String, Sesp > scope_let_map;
  Xn::Sys* sys;
  Xn::Spec* spec;
  SespCtx* spctx;
  Cx::Mem<Xn::PcSymm> pc_symm;
  Cx::Mem<Xn::PcSymmSpec> pc_symm_spec;

  ProtoconFile(Xn::Sys* sys, XFile* xf)
    : allgood( true )
    , text_nlines(0)
    , pc_symm(0)
    , pc_symm_spec(0)
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

  bool update_allgood(bool good);
  bool add_variables(Sesp vbl_name_sp, Sesp vbl_nmembs_sp, Sesp vbl_dom_sp,
                     Xn::Vbl::ShadowPuppetRole role);

  bool add_processes(Sesp pc_name, Sesp idx_name, Sesp npcs);

  bool add_constant(Sesp name_sp, Sesp val_sp);

  bool add_let(Sesp name_sp, Sesp val_sp);

  bool add_scope_let(Sesp name_sp, Sesp val_sp);

  void del_scope_let(Sesp name_sp);

  bool add_access(Sesp vbl_sp, Bit write);

  bool add_symmetric_links(Sesp let_names_sp, Sesp let_vals_list_sp);

  bool add_symmetric_access(Sesp let_names_sp, Sesp let_vals_list_sp, Sesp vbls_sp, Bit write);

  bool parse_action(Cx::PFmla& act_pf, Sesp act_sp);

  bool add_action(Sesp act_sp, Xn::Vbl::ShadowPuppetRole role);

  bool forbid_action(Sesp act_sp);

  bool add_pc_predicate(Sesp name_sp, Sesp val_sp);

  bool add_pc_legit(Sesp legit_sp);

  bool add_predicate(Sesp name_sp, Sesp val_sp);

  bool add_legit(Sesp legit_sp);

  bool string_expression(Cx::String& ss, Sesp a);

  bool eval(Cx::PFmla& pf, Sesp a);

  bool eval(Cx::IntPFmla& ipf, Sesp a);

  bool eval_int(int* ret, Sesp sp);

  bool eval_nat(uint* ret, Sesp sp);

  bool eval_gtz(uint* ret, Sesp sp);

  bool eval_vbl(Xn::Vbl** ret, Sesp sp);
  bool eval_vbl(Xn::Vbl** ret, Sesp b, Sesp c);

  bool lookup_pfmla(Cx::PFmla* ret, const Cx::String& name);
  bool lookup_int(int* ret, const Cx::String& name);
};

#endif

