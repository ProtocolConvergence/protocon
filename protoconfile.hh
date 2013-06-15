
#ifndef ProtoconFile_HH_
#define ProtoconFile_HH_

#include "cx/synhax.hh"
extern "C" {
#include "cx/sesp.h"
}
#include "xnsys.hh"

void ReadProtoconFile(Xn::Sys& sys, const char* fname);

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

  Map< Cx::String, uint > constant_map;
  Map< Cx::String, int > index_map;
  Map< Cx::String, const Xn::VblSymm* > vbl_map;
  Xn::Sys* sys;
  SespCtx* spctx;

  ProtoconFile(Xn::Sys* sys) {
    this->sys = sys;
    this->sys->invariant = true;
    spctx = make_SespCtx ();
  }

  ~ProtoconFile() {
    free_SespCtx (this->spctx);
  }

  bool add_variables(Sesp vbl_name_sp, Sesp vbl_nmembs_sp, Sesp vbl_dom_sp);

  bool add_processes(Sesp pc_name, Sesp idx_name, Sesp npcs);

  bool add_access(Sesp vbl_sp, Sesp pc_idx_sp, Bit write);

  bool add_legit(Sesp legit_sp, Sesp pc_idx_sp);

  bool add_legit(Sesp legit_sp);

  bool expression_chunks(Cx::Table<Cx::String>& chunks, Sesp a, const Cx::String& idx_name);

  bool eval(Cx::PFmla& pf, Sesp a);

  bool eval(Cx::IntPFmla& ipf, Sesp a);
};

#endif

