
#ifndef ProtoconFile_HH_
#define ProtoconFile_HH_

#include "cx/synhax.hh"
extern "C" {
#include "cx/sesp.h"
}
#include "xnsys.hh"

bool ReadProtoconFile(Xn::Sys& sys, const char* fname);

struct FinMeta
{
  //uint line;
  Sesp sp;
  Bit int_ck;
};

class ProtoconFile {
private:
  ProtoconFile(const ProtoconFile&);
  ProtoconFile& operator=(const ProtoconFile&);

public:

  bool allgood;
  Map< Cx::String, uint > constant_map;
  Map< Cx::String, Sesp > let_map;
  Map< Cx::String, int > index_map;
  Map< Cx::String, const Xn::VblSymm* > vbl_map;
  Xn::Sys* sys;
  SespCtx* spctx;

  ProtoconFile(Xn::Sys* sys)
    : allgood( true )
  {
    this->sys = sys;
    this->sys->invariant = true;
    spctx = make_SespCtx ();
  }

  ~ProtoconFile() {
    free_SespCtx (this->spctx);
  }

  bool add_variables(Sesp vbl_name_sp, Sesp vbl_nmembs_sp, Sesp vbl_dom_sp,
                     Xn::Vbl::ShadowPuppetRole role);

  bool add_processes(Sesp pc_name, Sesp idx_name, Sesp npcs);

  bool add_let(Sesp name_sp, Sesp val_sp);

  bool add_access(Sesp vbl_sp, Sesp pc_idx_sp, Bit write);

  bool add_action(Sesp act_sp, Sesp pc_idx_sp);

  bool add_legit(Sesp legit_sp, Sesp pc_idx_sp);

  bool add_legit(Sesp legit_sp);

  bool expression(Cx::String& expression, Sesp a);
  bool expression_chunks(Cx::Table<Cx::String>& chunks, Sesp a, const Cx::String& idx_name);

  bool eval(Cx::PFmla& pf, Sesp a);

  bool eval(Cx::IntPFmla& ipf, Sesp a);

  bool eval_int(int* ret, Sesp sp);

  bool eval_gtz(uint* ret, Sesp sp);

  bool eval_vbl(Xn::Vbl** ret, Sesp sp);
  bool eval_vbl(Xn::Vbl** ret, Sesp b, Sesp c);

  bool lookup_int(int* ret, const Cx::String& name);
};

#endif

