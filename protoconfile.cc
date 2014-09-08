

#include "protoconfile.hh"
#include "cx/bittable.hh"

  bool
ProtoconFile::update_allgood(bool good)
{
  if (!allgood)  return false;
  if (good)  return true;
  allgood = false;
  DBog1( "Something terribly wrong before line:%u", this->text_nlines );
  return false;
}

  bool
ProtoconFile::add_variables(Sesp vbl_name_sp, Sesp vbl_nmembs_sp, Sesp vbl_dom_sp,
                            Xn::Vbl::ShadowPuppetRole role)
{
  bool good = true;
  const char* name = 0;
  uint nmembs = 0;
  uint domsz = 0;

  name = ccstr_of_Sesp (vbl_name_sp);
  if (LegitCk(name, good, "")) {}
  if (LegitCk(eq_cstr ("NatDom", ccstr_of_Sesp (car_of_Sesp (vbl_nmembs_sp))), good, "")) {}
  if (LegitCk(eq_cstr ("NatDom", ccstr_of_Sesp (car_of_Sesp (vbl_dom_sp))), good, "")) {}

  if (LegitCk(eval_gtz (&nmembs, cadr_of_Sesp (vbl_nmembs_sp)), good, ""))
  {}
  if (LegitCk(eval_gtz (&domsz, cadr_of_Sesp (vbl_dom_sp)), good, ""))
  {
    Xn::VblSymm* symm = sys->topology.add_variables(name, nmembs, domsz, role);
    vbl_map[name] = symm;
    symm->spec->domsz_expression = "";
    string_expression (symm->spec->domsz_expression, cadr_of_Sesp (vbl_dom_sp));
    symm->spec->nmembs_expression = "";
    string_expression (symm->spec->nmembs_expression, cadr_of_Sesp (vbl_nmembs_sp));
  }
  return update_allgood (good);
}

  bool
ProtoconFile::add_processes(Sesp pc_name, Sesp idx_name, Sesp npcs)
{
  Claim2( index_map.sz() ,==, 0 );
  bool good = true;
  const char* name_a = ccstr_of_Sesp (pc_name);
  const char* name_b = ccstr_of_Sesp (idx_name);
  if (LegitCk(name_a && name_b, good, "")) {
    uint domsz = 0;
    if (LegitCk(eval_nat (&domsz, cadr_of_Sesp (npcs)), good, "")) {
      this->pc_symm =
        sys->topology.add_processes(name_a, name_b, (uint) domsz);
      this->pc_symm_spec = pc_symm->spec;
      pc_symm_spec->nmembs_expression = "";
      string_expression (pc_symm_spec->nmembs_expression, cadr_of_Sesp (npcs));
    }
  }
  if (good) {
  }
  return update_allgood (good);
}

  bool
ProtoconFile::add_constant(Sesp name_sp, Sesp val_sp)
{
  Sign good = 1;

  const char* name = ccstr_of_Sesp (name_sp);
  DoLegit( good, "" )
    good = !!name;
  Xn::NatMap val(1);
  DoLegit(good, "evaluating int")
    good = eval_int (&val.membs[0], val_sp);
  DoLegit( good, "finding expression" )
    good = string_expression (val.expression, val_sp);
  DoLegit( good, "" )
    if (!spec->constant_map.key_ck(name))
      spec->constant_map.add(name, val);

  return update_allgood (good);
}

  bool
ProtoconFile::add_let(Sesp name_sp, Sesp val_sp)
{
  Sign good = 1;
  const char* name = ccstr_of_Sesp (name_sp);
  DoLegit(  good, "" )
    good = !!name;

  const Cx::String& idx_name = pc_symm_spec->idx_name;
  Xn::NatMap let_vals( pc_symm->membs.sz() );
  for (uint i = 0; good && i < pc_symm->membs.sz(); ++i) {
    index_map[idx_name] = i;
    DoLegit( good, "" )
      good = eval_int (&let_vals.membs[i], val_sp);
  }
  index_map.erase(idx_name);
  DoLegit( good, "finding expression" )
    good = string_expression (let_vals.expression, val_sp);
  DoLegit( good, "" )
    pc_symm_spec->let_map.add(name, let_vals);
  return update_allgood (good);
}

  bool
ProtoconFile::add_scope_let(Sesp name_sp, Sesp val_sp)
{
  Sign good = 1;
  const char* name = ccstr_of_Sesp (name_sp);
  DoLegit(  good, "" )
    good = !!name;

  DoLegit(  good, "" )
    scope_let_map[name] = val_sp;

  return update_allgood (good);
}

  void
ProtoconFile::del_scope_let(Sesp name_sp)
{
  scope_let_map.erase(ccstr_of_Sesp(name_sp));
}

  bool
ProtoconFile::add_access(Sesp vbl_sp, Bit write)
{
  bool legit = true;
  const char* vbl_name = 0;
  Sesp vbl_idx_sp = 0;
  Xn::Net& topo = sys->topology;
  const Xn::VblSymm* vbl_symm = 0;

  // (aref vbl_name vbl_idx)
  vbl_name = ccstr_of_Sesp (cadr_of_Sesp (vbl_sp));
  if (LegitCk( vbl_name, legit, "" ))
  {
    const Xn::VblSymm** tmp = 0;
    tmp = vbl_map.lookup(vbl_name);
    if (tmp)  vbl_symm = *tmp;
  }
  if (LegitCk( vbl_symm, legit, "" ))
  {
    vbl_idx_sp = caddr_of_Sesp (vbl_sp);
  }

  if (LegitCk( topo.pc_symms.sz() > 0, legit, "" ))
  {
    Cx::IntPFmla ipf;
    const Cx::String& idx_name = pc_symm_spec->idx_name;
    Xn::NatMap indices( pc_symm->membs.sz() );

    for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
      index_map[idx_name] = i;
      if (LegitCk( eval_int (&indices.membs[i], vbl_idx_sp), legit, "" )) {}
    }
    index_map.erase(idx_name);

    if (legit) {
      bool bstat = string_expression(indices.expression, vbl_idx_sp);
      if (LegitCk(bstat, legit, "string_expression()"))
      {}
    }

    if (legit) {
      if (write) {
        topo.add_write_access(+pc_symm, vbl_symm, indices);
      }
      else {
        topo.add_read_access(+pc_symm, vbl_symm, indices);
      }
    }
  }

  return update_allgood (legit);
}

  bool
ProtoconFile::add_symmetric_links(Sesp let_names_sp, Sesp let_vals_list_sp)
{
  Sign good = 1;
  pc_symm_spec->link_symmetries.push(Xn::LinkSymmetry(sz_of_Sesp (let_vals_list_sp)));
  Xn::LinkSymmetry& link_symmetry = pc_symm_spec->link_symmetries.top();
  if (sz_of_Sesp (let_names_sp) == 1) {
    link_symmetry.let_expression = ccstr_of_Sesp (car_of_Sesp (let_names_sp));
    Sesp let_vals_sp = let_vals_list_sp;
    while (!nil_ck_Sesp (let_vals_sp)) {
      link_symmetry.multiset_expression.push_delim("", ", ");
      Cx::String val_expression;
      string_expression(val_expression, caar_of_Sesp (let_vals_sp));
      link_symmetry.multiset_expression += val_expression;
      let_vals_sp = cdr_of_Sesp (let_vals_sp);
    }
    return update_allgood (good);
  }

  Sesp let_name_sp = let_names_sp;
  while (!nil_ck_Sesp (let_name_sp)) {
    link_symmetry.let_expression.push_delim("(", ", ");

    link_symmetry.let_expression += ccstr_of_Sesp (car_of_Sesp (let_name_sp));
    let_name_sp = cdr_of_Sesp (let_name_sp);
  }
  link_symmetry.let_expression += ")";

  Sesp let_vals_sp = let_vals_list_sp;
  while (!nil_ck_Sesp (let_vals_sp)) {
    link_symmetry.multiset_expression.push_delim("", ", ");

    Cx::String tuple_expression;
    Sesp let_val_sp = car_of_Sesp (let_vals_sp);
    while (!nil_ck_Sesp (let_val_sp)) {
      tuple_expression.push_delim("(", ", ");

      Cx::String val_expression;
      DoLegit( good, "" )
        good = string_expression(val_expression, car_of_Sesp (let_val_sp));
      if (!good)  break;
      tuple_expression += val_expression;
      let_val_sp = cdr_of_Sesp (let_val_sp);
    }
    tuple_expression += ")";

    link_symmetry.multiset_expression += tuple_expression;
    let_vals_sp = cdr_of_Sesp (let_vals_sp);
  }

  return update_allgood (good);
}

  bool
ProtoconFile::add_symmetric_access(Sesp let_names_sp, Sesp let_vals_list_sp,
                                   Sesp vbls_sp, Bit write)
{
  Sign good = 1;
  Xn::LinkSymmetry& link_symmetry = pc_symm_spec->link_symmetries.top();

  while (!nil_ck_Sesp (vbls_sp)) {
    Sesp let_vals_sp = let_vals_list_sp;
    Cx::Table<uint> vbl_idcs;
    while (!nil_ck_Sesp (let_vals_sp)) {
      Sesp let_name_sp = let_names_sp;
      Sesp let_val_sp = car_of_Sesp (let_vals_sp);
      while (good && !nil_ck_Sesp (let_name_sp)) {
        DoLegit( good, "Tuple must be of the same size!" )
          good = !nil_ck_Sesp (let_val_sp);
        if (!good)  break;

        add_scope_let(car_of_Sesp (let_name_sp), car_of_Sesp (let_val_sp));
        let_name_sp = cdr_of_Sesp (let_name_sp);
        let_val_sp = cdr_of_Sesp (let_val_sp);
      }
      DoLegit( good, "Tuples must be of the same size!" )
        good = nil_ck_Sesp (let_val_sp);
      if (!good)  break;

      vbl_idcs.push(pc_symm_spec->rvbl_symms.sz());
      add_access(car_of_Sesp (vbls_sp), write);

      let_name_sp = let_names_sp;
      while (!nil_ck_Sesp (let_name_sp)) {
        del_scope_let(car_of_Sesp (let_name_sp));
        let_name_sp = cdr_of_Sesp (let_name_sp);
      }
      let_vals_sp = cdr_of_Sesp (let_vals_sp);
    }
    if (!good)  break;

    Cx::String index_expression;
    string_expression(index_expression, caddar_of_Sesp (vbls_sp));
    link_symmetry.add_link_symmetry(vbl_idcs, index_expression);
    vbls_sp = cdr_of_Sesp (vbls_sp);
  }
  return update_allgood (good);
}

  bool
ProtoconFile::parse_action(Cx::PFmla& act_pf, Cx::Table<Cx::PFmla>& pc_xns, Sesp act_sp, bool selfloop)
{
  Sign good = 1;
  Claim( pc_symm );
  const Xn::Net& topo = sys->topology;
  act_pf = false;
  pc_xns.resize(pc_symm->membs.sz());
  for (uint i = 0; good && i < pc_symm->membs.sz(); ++i) {
    pc_xns[i] = false;
  }

  const Cx::String& idx_name = pc_symm_spec->idx_name;
  for (uint pcidx = 0; good && pcidx < pc_symm->membs.sz(); ++pcidx) {
    const Xn::Pc& pc = *pc_symm->membs[pcidx];
    index_map[idx_name] = pcidx;
    Cx::PFmla guard_pf;
    DoLegit( good, "eval guard" )
      good = eval(guard_pf, cadr_of_Sesp (act_sp));
    if (!good)  continue;

    Cx::PFmla assign_pf( true );
    Sesp assign_sp = cddr_of_Sesp (act_sp);

    Cx::BitTable wvbl_assigned( pc.wvbls.sz(), (selfloop ? 0 : 1) );

    while (!nil_ck_Sesp (assign_sp)) {
      Sesp sp = car_of_Sesp (assign_sp);
      Claim( list_ck_Sesp (sp) );

      bool all_wild = false;
      if (eq_cstr ("wild", ccstr_of_Sesp (car_of_Sesp (sp)))) {
        all_wild = true;
      }
      else {
        Claim( eq_cstr (":=", ccstr_of_Sesp (car_of_Sesp (sp))) );
      }

      Sesp vbl_sp = cadr_of_Sesp (sp);
      Sesp val_sp = caddr_of_Sesp (sp);
      assign_sp = cdr_of_Sesp (assign_sp);

      Xn::Vbl* vbl = 0;
      Cx::IntPFmla val;

      DoLegit( good, "eval variable" )
      {
        if (!all_wild)
          good = eval_vbl(&vbl, vbl_sp);
      }

      bool wild = false;
      DoLegit( good, "eval value" )
      {
        if (all_wild) {
        }
        else if (list_ck_Sesp(val_sp) && eq_cstr ("wild", ccstr_of_Sesp (car_of_Sesp (val_sp)))) {
          wild = true;
        }
        else {
          good = eval(val, val_sp);
        }
      }

      DoLegit( good, "non-writable variable in assignment" )
      {
        bool found = false;
        for (uint i = 0; i < pc.wvbls.sz(); ++i) {
          if (all_wild) {
            found = true;
            wvbl_assigned[i] = 1;
          }
          else if (pc.wvbls[i] == vbl) {
            found = true;
            wvbl_assigned[i] = 1;
            break;
          }
        }
        good = found;
      }
      if (!good)  break;

      if (all_wild) {
        assign_pf = true;
      }
      else if (!wild) {
        const Cx::PFmlaVbl& pf_vbl = topo.pfmla_vbl(*vbl);
        val %= vbl->symm->domsz;
        assign_pf &= pf_vbl.img_eq(val);
      }

    }

    for (uint i = 0; i < pc.wvbls.sz(); ++i) {
      if (!wvbl_assigned[i]) {
        const Cx::PFmlaVbl& pf_vbl = topo.pfmla_vbl(*pc.wvbls[i]);
        assign_pf &= pf_vbl.img_eq(pf_vbl);
      }
    }

    pc_xns[pcidx] = guard_pf & assign_pf;
    act_pf |= pc_xns[pcidx] & pc.act_unchanged_pfmla;
  }
  if (good)
    index_map.erase(idx_name);
  return update_allgood (good);
}

  bool
ProtoconFile::add_action(Sesp act_sp, Xn::Vbl::ShadowPuppetRole role)
{
  if (!allgood)  return false;
  Sign good = 1;
  Claim( pc_symm );
  Xn::Net& topo = sys->topology;

  DoLegit( good, "" )
  {
    if (role != Xn::Vbl::Puppet) {
      Cx::String act_expression;
      good = string_expression (act_expression, act_sp);
      if (good) {
        pc_symm_spec->shadow_act_strings.push(act_expression);
      }
    }
  }

  Cx::PFmla act_pf( false );
  Cx::Table<Cx::PFmla> pc_xns;
  DoLegit( good, "parse action" )
    good = parse_action(act_pf, pc_xns, act_sp, true);

  if (good) {
    for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
      pc_symm->membs[i]->puppet_xn |= pc_xns[i];
    }
  }

  if (false)
  DoLegit(good, "self-loop")
    good = !act_pf.overlap_ck(topo.identity_xn);

  DoLegit(good, "")
  {
    if (role != Xn::Vbl::Puppet) {
      const Cx::PFmla& shadow_act_pf =
        (topo.smooth_pure_puppet_vbls(act_pf) -
         topo.smooth_pure_puppet_vbls(topo.identity_xn));
      pc_symm->shadow_pfmla |= shadow_act_pf;
      sys->shadow_pfmla |= shadow_act_pf;
    }


    if (role != Xn::Vbl::Shadow) {
#if 0
      uint rep_pcidx = 0;
      pc_symm->representative(&rep_pcidx);
      pc_symm->direct_pfmla |= pc_xns[rep_pcidx];
#else
      pc_symm->direct_pfmla |= act_pf;
#endif
      sys->direct_pfmla |= act_pf;
    }
  }

  return update_allgood (good);
}

  bool
ProtoconFile::forbid_action(Sesp act_sp)
{
  Sign good = 1;
  Claim( pc_symm );

  DoLegit( good, "" )
  {
    Cx::String act_expression;
    good = string_expression (act_expression, act_sp);
    if (good) {
      pc_symm_spec->forbid_act_strings.push(act_expression);
    }
  }

  Cx::PFmla act_pf( false );
  Cx::Table<Cx::PFmla> pc_xns;
  DoLegit( good, "parse action" ) {
    good = parse_action(act_pf, pc_xns, act_sp, false);
  }

  DoLegit( good, "" ) {
    uint rep_pcidx = 0;
    pc_symm->representative(&rep_pcidx);
    pc_symm->forbid_pfmla |= pc_xns[rep_pcidx];
  }

  return update_allgood (good);
}

  bool
ProtoconFile::permit_action(Sesp act_sp)
{
  Sign good = 1;
  Claim( pc_symm );

  DoLegit( good, "" )
  {
    Cx::String act_expression;
    good = string_expression (act_expression, act_sp);
    if (good) {
      pc_symm_spec->permit_act_strings.push(act_expression);
    }
  }

  Cx::PFmla act_pf( false );
  Cx::Table<Cx::PFmla> pc_xns;
  DoLegit( good, "parse action" ) {
    good = parse_action(act_pf, pc_xns, act_sp, false);
  }

  DoLegit( good, "" ) {
    uint rep_pcidx = 0;
    pc_symm->representative(&rep_pcidx);
    pc_symm->permit_pfmla &= pc_xns[rep_pcidx];
  }

  return update_allgood (good);
}

  bool
ProtoconFile::add_pc_predicate(Sesp name_sp, Sesp val_sp)
{
  Sign good = 1;
  const char* name = ccstr_of_Sesp (name_sp);
  DoLegit(  good, "" )
    good = !!name;

  const Cx::String& idx_name = pc_symm_spec->idx_name;
  Xn::NatPredicateMap let_vals( pc_symm->membs.sz() );
  for (uint i = 0; good && i < pc_symm->membs.sz(); ++i) {
    index_map[idx_name] = i;
    DoLegit( good, "" )
      good = eval (let_vals.membs[i], val_sp);
  }
  index_map.erase(idx_name);
  DoLegit( good, "finding expression" )
    good = string_expression (let_vals.expression, val_sp);
  DoLegit( good, "" )
    pc_symm->predicate_map.add(name, let_vals);
  return update_allgood (good);
}

  bool
ProtoconFile::add_pc_assume(Sesp assume_sp)
{
  Sign good = 1;

  const Cx::String& idx_name = pc_symm_spec->idx_name;
  Cx::PFmla pf;

  for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
    index_map[idx_name] = i;
    DoLegit( good, "" )
      good = eval(pf, assume_sp);

    if (!good)  break;
    sys->closed_assume &= pf;
  }

  Cx::String assume_expression;
  DoLegit( good, "" )
    good = string_expression(assume_expression, assume_sp);

  DoLegit( good, "" )
  {
    if (!pc_symm_spec->closed_assume_expression.empty_ck()) {
      pc_symm_spec->closed_assume_expression =
        Cx::String("(") + pc_symm_spec->closed_assume_expression + ") && ";
    }
    pc_symm_spec->closed_assume_expression += assume_expression;
  }
  index_map.erase(idx_name);
  return update_allgood (good);
}

  bool
ProtoconFile::add_pc_legit(Sesp legit_sp)
{
  Sign good = 1;

  const Cx::String& idx_name = pc_symm_spec->idx_name;
  Cx::PFmla pf;

  for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
    index_map[idx_name] = i;
    DoLegit( good, "" )
      good = eval(pf, legit_sp);

    DoLegit( good, "" )
    {
      sys->invariant &= pf;
      pc_symm->membs[i]->invariant &= pf;
    }
  }

  Cx::String invariant_expression;
  DoLegit( good, "" )
    good = string_expression(invariant_expression, legit_sp);

  DoLegit( good, "" )
  {
    if (!pc_symm_spec->invariant_expression.empty_ck()) {
      pc_symm_spec->invariant_expression =
        Cx::String("(") + pc_symm_spec->invariant_expression + ") && ";
    }
    pc_symm_spec->invariant_expression += invariant_expression;
  }
  index_map.erase(idx_name);
  return update_allgood (good);
}

  bool
ProtoconFile::finish_pc_def()
{
  bool good = true;
  this->pc_symm = 0;
  this->pc_symm_spec = 0;
  return update_allgood (good);
}

  bool
ProtoconFile::add_predicate(Sesp name_sp, Sesp val_sp)
{
  Sign good = 1;
  const char* name = ccstr_of_Sesp (name_sp);
  DoLegit(  good, "" )
    good = !!name;

  Cx::PFmla pf(false);
  Cx::String expression;
  DoLegit( good, "" )
    good = eval(pf, val_sp);

  DoLegit( good, "finding expression" )
    good = string_expression (expression, val_sp);

  DoLegit( good, "" )
    sys->predicate_map.add(name, pf, expression);

  return update_allgood (good);
}

  bool
ProtoconFile::add_assume(Sesp assume_sp)
{
  Sign good = 1;

  Cx::PFmla pf;
  DoLegit( good, "parse invariant" )
    good = eval(pf, assume_sp);

  DoLegit( good, "" )
    sys->closed_assume &= pf;

  Cx::String str;
  DoLegit( good, "convert invariant expression to string" )
    good = string_expression(str, assume_sp);

  DoLegit( good, "" ) {
    if (spec->closed_assume_expression != "") {
      spec->closed_assume_expression =
        Cx::String("(") + spec->closed_assume_expression + ")\n  &&\n  ";
    }
    spec->closed_assume_expression += str;
  }

  return update_allgood (good);
}

  bool
ProtoconFile::add_legit(Sesp legit_sp)
{
  Sign good = 1;

  Cx::PFmla pf;
  DoLegit( good, "parse invariant" )
    good = eval(pf, legit_sp);

  DoLegit( good, "" )
    sys->invariant &= pf;

  Cx::String invariant_expression;
  DoLegit( good, "convert invariant expression to string" )
    good = string_expression(invariant_expression, legit_sp);

  DoLegit( good, "" ) {
    if (spec->invariant_expression != "") {
      spec->invariant_expression =
        Cx::String("(") + spec->invariant_expression + ")\n  &&\n  ";
    }
    spec->invariant_expression += invariant_expression;
  }

  return update_allgood (good);
}

  bool
ProtoconFile::string_expression(Cx::String& ss, Sesp a)
{
  Sign good = 1;

  const char* key = 0;

  DoLegit( good, "" )
    good = !!a;

  DoLegit( good, "" )
  {
    const char* name = ccstr_of_Sesp (a);
    if (name)
    {
      {
        Sesp* val_sp = scope_let_map.lookup(name);
        if (val_sp) {
          return string_expression(ss, *val_sp);
        }
      }
      ss += name;
      return good;
    }

    uint u = 0;
    if (uint_of_Sesp (a, &u))
    {
      ss += u;
      return good;
    }

    key = ccstr_of_Sesp (car_of_Sesp (a));
  }

  DoLegit( good, "ccstr_of_Sesp()" )
    good = !!key;

  if (!good) {
  }
  else if (eq_cstr (key, "(bool)") ||
           eq_cstr (key, "(int)")) {
    ss += "(";
    string_expression(ss, cadr_of_Sesp (a));
    ss += ")";
  }
  else if (eq_cstr (key, "!")) {
    ss += "!";
    string_expression (ss, cadr_of_Sesp (a));
  }
  else if (eq_cstr (key, "negate")) {
    ss += "-";
    string_expression (ss, cadr_of_Sesp (a));
  }
  else if (eq_cstr (key, "&&") ||
           eq_cstr (key, "||") ||
           eq_cstr (key, "=>") ||
           eq_cstr (key, "<") ||
           eq_cstr (key, "<=") ||
           eq_cstr (key, "!=") ||
           eq_cstr (key, "==") ||
           eq_cstr (key, ">=") ||
           eq_cstr (key, ">") ||
           eq_cstr (key, ":=") ||
           eq_cstr (key, "+") ||
           eq_cstr (key, "-") ||
           eq_cstr (key, "*") ||
           eq_cstr (key, "/") ||
           eq_cstr (key, "%") ||
           eq_cstr (key, "^")) {
    bool pad =
      (eq_cstr (key, "&&") ||
       eq_cstr (key, "||") ||
       eq_cstr (key, "=>"));
    string_expression (ss, cadr_of_Sesp (a));
    if (pad)  ss += " ";
    ss += key;
    if (pad)  ss += " ";
    string_expression (ss, caddr_of_Sesp (a));
  }
  else if (eq_cstr (key, "xnor")) {
    string_expression (ss, cadr_of_Sesp (a));
    ss += "==";
    string_expression (ss, caddr_of_Sesp (a));
  }
  else if (eq_cstr (key, "xor")) {
    string_expression (ss, cadr_of_Sesp (a));
    ss += "!=";
    string_expression (ss, caddr_of_Sesp (a));
  }
  else if (eq_cstr (key, "-->")) {
    string_expression (ss, cadr_of_Sesp (a));
    ss += " -->";
    for (Sesp b = cddr_of_Sesp (a); !nil_ck_Sesp (b); b = cdr_of_Sesp (b)) {
      ss += " ";
      string_expression (ss, car_of_Sesp (b));
      ss += ";";
    }
  }
  else if (eq_cstr (key, "wild"))
  {
    ss += "_";
  }
  else if (eq_cstr (key, "NatDom")) {
    ss += "Nat % ";
    string_expression (ss, cadr_of_Sesp (a));
  }
  else if (eq_cstr (key, "aref")) {
    ss += ccstr_of_Sesp (cadr_of_Sesp (a));
    ss += "[";
    string_expression (ss, caddr_of_Sesp (a));
    ss += "]";
  }
  else if (eq_cstr (key, "iif")) {
    ss += "if ";
    string_expression (ss, cadr_of_Sesp (a));
    ss += " then ";
    string_expression (ss, caddr_of_Sesp (a));
    ss += " else ";
    string_expression (ss, cadddr_of_Sesp (a));
  }
  else if (eq_cstr (key, "forall") ||
           eq_cstr (key, "exists") ||
           eq_cstr (key, "unique")
          )
  {
    ss += key;
    ss += " ";
    ss += ccstr_of_Sesp (cadr_of_Sesp (a));
    ss += " <- ";
    string_expression (ss, caddr_of_Sesp (a));
    ss += " : ";
    string_expression (ss, cadddr_of_Sesp (a));
  }
  else {
    good = false;
    DBog1( "No matching string, key is: \"%s\"", key );
  }

  return update_allgood (good);
}


  bool
ProtoconFile::eval(Cx::PFmla& pf, Sesp a)
{
  bool good = true;

  if (LegitCk(a, good, ""))
  {
    const char* name = ccstr_of_Sesp (a);
    if (name)
    {
      if (LegitCk( lookup_pfmla(&pf, name), good, "lookup_pfmla()" )) {
      }
      if (LegitCk( good, allgood, "" )) {}
      return good;
    }
  }

  Sesp b = cdr_of_Sesp (a);
  Sesp c = cdr_of_Sesp (b);
  Sesp d = cdr_of_Sesp (c);

  a = car_of_Sesp (a);
  b = car_of_Sesp (b);
  c = car_of_Sesp (c);
  d = car_of_Sesp (d);

  const char* key = ccstr_of_Sesp (a);

  // Temporaries.
  Cx::IntPFmla ipf_b;
  Cx::IntPFmla ipf_c;
  Cx::PFmla pf_b;
  Cx::PFmla pf_c;

  //DBog1("key is: %s", key);

  if (eq_cstr (key, "(bool)")) {
    if (LegitCk( eval(pf, b), good, "" )) {
      // That's all.
    }
  }
  else if (eq_cstr (key, "!")) {
    if (LegitCk( eval(pf, b), good, "" )) {
      pf = !pf;
    }
  }
  else if (eq_cstr (key, "&&")) {
    if (LegitCk( eval(pf, b), good, "" )) {
      if (LegitCk( eval(pf_c, c), good, "" )) {
        pf &= pf_c;
      }
    }
  }
  else if (eq_cstr (key, "||")) {
    if (LegitCk( eval(pf, b), good, "" )) {
      if (LegitCk( eval(pf_c, c), good, "" )) {
        pf |= pf_c;
      }
    }
  }
  else if (eq_cstr (key, "=>")) {
    if (LegitCk( eval(pf, b), good, "" )) {
      if (LegitCk( eval(pf_c, c), good, "" )) {
        pf = ~pf | pf_c;
      }
    }
  }
  else if (eq_cstr (key, "xnor")) {
    if (LegitCk( eval(pf, b), good, "" )) {
      if (LegitCk( eval(pf_c, c), good, "" )) {
        pf.defeq_xnor(pf_c);
      }
    }
  }
  else if (eq_cstr (key, "xor")) {
    if (LegitCk( eval(pf, b), good, "" )) {
      if (LegitCk( eval(pf_c, c), good, "" )) {
        pf ^= pf_c;
      }
    }
  }
  else if (eq_cstr (key, "<" ) ||
           eq_cstr (key, "<=") ||
           eq_cstr (key, "!=") ||
           eq_cstr (key, "==") ||
           eq_cstr (key, ">=") ||
           eq_cstr (key, ">" ))
  {
    if (LegitCk( eval(ipf_b, b), good, "" )) {
      if (LegitCk( eval(ipf_c, c), good, "" )) {
        if      (eq_cstr (key, "<" ))  pf = (ipf_b < ipf_c);
        else if (eq_cstr (key, "<="))  pf = (ipf_b <= ipf_c);
        else if (eq_cstr (key, "!="))  pf = (ipf_b != ipf_c);
        else if (eq_cstr (key, "=="))  pf = (ipf_b == ipf_c);
        else if (eq_cstr (key, ">="))  pf = (ipf_b >= ipf_c);
        else if (eq_cstr (key, ">" ))  pf = (ipf_b > ipf_c);
      }
    }
  }
  else if (eq_cstr (key, "forall") ||
           eq_cstr (key, "exists") ||
           eq_cstr (key, "unique")
          )
  {
    const char* idxname = ccstr_of_Sesp (b);
    if (LegitCk( idxname, good, "" ))
    {}
    if (LegitCk( eval(ipf_c, c), good, "" ))
    {}
    if (LegitCk( ipf_c.vbls.sz() == 0, good, "" )) {
      const uint n = ipf_c.state_map.sz();

      if (eq_cstr (key, "forall")) {
        pf = true;
      }
      else if (eq_cstr (key, "exists")) {
        pf = false;
      }
      else {
        pf = false;
        pf_b = false;
      }

      for (uint i = 0; good && i < n; ++i) {
        index_map[idxname] = ipf_c.state_map[i];
        if (LegitCk( eval(pf_c, d), good, "" ))
        {
          if (eq_cstr (key, "forall")) {
            pf &= pf_c;
          }
          else if (eq_cstr (key, "exists")) {
            pf |= pf_c;
          }
          else {
            pf -= (pf_c & pf_b);
            pf |= (pf_c - pf_b);
            pf_b |= pf_c;
          }
        }
      }
      index_map.erase(idxname);
    }
#if 0
    if (LegitCk( ipf_c.vbls.sz() == 0, good, "" )) {
      const uint n = ipf_c.state_map.sz();

      Cx::Table< Cx::PFmla > pfmlas( n );

      for (uint i = 0; good && i < n; ++i) {
        index_map[idxname] = ipf_c.state_map[i];
        if (LegitCk( eval(pfmlas[i], d), good, "" ))
        {}
      }

      if (good) {
        if (eq_cstr (key, "forall")) {
          pf = true;
          for (uint i = 0; i < n; ++i) {
            pf &= pfmlas[i];
          }
        }
        else if (eq_cstr (key, "exists")) {
          pf = false;
          for (uint i = 0; i < n; ++i) {
            pf |= pfmlas[i];
          }
        }
        else {
          pf = false;
          for (uint i = 0; i < n; ++i) {
            Cx::PFmla conj( pfmlas[i] );
            for (uint j = 0; j < n; ++j) {
              if (j != i) {
                conj &= ~ pfmlas[j];
              }
            }
            pf |= conj;
          }
        }
      }

      index_map.erase(idxname);
    }
#endif
  }
  else {
    good = false;
    DBog1( "No matching string, key is: \"%s\"", key );
  }

  return update_allgood (good);
}


/**
 * Second eval() function.
 * This one is for IntPFmlas.
 **/
  bool
ProtoconFile::eval(Cx::IntPFmla& ipf, Sesp a)
{
  bool good = true;

  if (LegitCk(a, good, ""))
  {
    const char* name = ccstr_of_Sesp (a);
    if (name)
    {
      {
        Sesp* val_sp = scope_let_map.lookup(name);
        if (val_sp) {
          if (LegitCk( eval(ipf, *val_sp), good, "evaluating scope'd let" )) {
            return true;
          }
          return update_allgood (false);
        }
      }

      int val = 0;
      if (LegitCk( lookup_int(&val, name), good, "lookup_int()" )) {
        ipf = Cx::IntPFmla( val );
        //DBog2("index %s is: %d", name, *val);
      }
      if (LegitCk( good, allgood, "" )) {}
      return good;
    }

    uint x = 0;
    if (uint_of_Sesp (a, &x)) {
      ipf = Cx::IntPFmla( x );
      //DBog1("int is: %u", x);
      return good;
    }
  }

  Sesp b = cdr_of_Sesp (a);
  Sesp c = cdr_of_Sesp (b);
  Sesp d = cdr_of_Sesp (c);

  a = car_of_Sesp (a);
  b = car_of_Sesp (b);
  c = car_of_Sesp (c);
  d = car_of_Sesp (d);

  const char* key = ccstr_of_Sesp (a);

  Cx::IntPFmla ipf_c;

  if (LegitCk(a, good, "car_of_Sesp()"))
  {}
  if (LegitCk(key, good, "ccstr_of_Sesp()"))
  {
    //DBog1("key is: %s", key);
  }
  if (false && !good)
  {
    if (nil_ck_Sesp (a))
      DBog0("it's nil");
    if (list_ck_Sesp (a))
      DBog0("it's a list");
    if (atom_ck_Sesp (a))
      DBog0("it's an atom");
    if (a) {
      DBog1( "a->kind->vt->kind_name = %s", a->kind->vt->kind_name );
    }
  }

  if (!good)
  {}
  else if (eq_cstr (key, "(int)")) {
    if (LegitCk( eval(ipf, b), good, "" )) {
      // That's all.
    }
  }
  else if (eq_cstr (key, "negate")) {
    if (LegitCk( eval(ipf, b), good, "" )) {
      ipf.negate();
    }
  }
  else if (eq_cstr (key, "+")) {
    if (LegitCk( eval(ipf, b), good, "" )) {
      if (LegitCk( eval(ipf_c, c), good, "" )) {
        ipf += ipf_c;
      }
    }
  }
  else if (eq_cstr (key, "-")) {
    if (LegitCk( eval(ipf, b), good, "" )) {
      if (LegitCk( eval(ipf_c, c), good, "" )) {
        ipf -= ipf_c;
      }
    }
  }
  else if (eq_cstr (key, "*")) {
    if (LegitCk( eval(ipf, b), good, "" )) {
      if (LegitCk( eval(ipf_c, c), good, "" )) {
        ipf *= ipf_c;
      }
    }
  }
  else if (eq_cstr (key, "/")) {
    if (LegitCk( eval(ipf, b), good, "" )) {
      if (LegitCk( eval(ipf_c, c), good, "" )) {
        ipf /= ipf_c;
      }
    }
  }
  else if (eq_cstr (key, "%")) {
    if (LegitCk( eval(ipf, b), good, "" )) {
      if (LegitCk( eval(ipf_c, c), good, "" )) {
        ipf %= ipf_c;
      }
    }
  }
  else if (eq_cstr (key, "^")) {
    if (LegitCk( eval(ipf, b), good, "" )) {
      if (LegitCk( eval(ipf_c, c), good, "" )) {
        ipf.defeq_pow(ipf_c);
      }
    }
  }
  else if (eq_cstr (key, "NatDom")) {
    uint domsz = 0;
    if (LegitCk(eval_gtz (&domsz, b), good, "")) {
      ipf = Cx::IntPFmla( 1, 0, domsz );
    }
  }
  else if (eq_cstr (key, "iif")) {
    Cx::PFmla pf( true );
    if (LegitCk(eval(pf, b), good, "")) {
      if (pf.tautology_ck()) {
        b = c;
      }
      else if (!pf.sat_ck()) {
        b = d;
      }
      else {
        DBog0("The conditional is not constant!");
        good = false;
      }
    }
    if (LegitCk(eval(ipf, b), good, "")) {
    }
  }
  else if (eq_cstr (key, "aref")) {
    Xn::Vbl* vbl = 0;
    if (LegitCk( eval_vbl(&vbl, b, c), good, "" )) {
      ipf = Cx::IntPFmla(sys->topology.pfmla_vbl(*vbl));
    }
  }
  else {
    good = false;
    DBog1( "No matching string, key is: \"%s\"", key );
  }

  return update_allgood (good);
}

  bool
ProtoconFile::eval_int(int* ret, Sesp sp)
{
  bool legit = true;
  Cx::IntPFmla ipf;
  if (LegitCk( eval(ipf, sp), legit, "" )) {
    if (LegitCk( ipf.state_map.sz() == 1, legit, "" )) {
      *ret = ipf.state_map[0];
    }
  }
  return update_allgood (legit);
}

  bool
ProtoconFile::eval_nat(uint* ret, Sesp sp)
{
  int x = 0;
  bool legit = eval_int (&x, sp);
  if (LegitCk( x >= 0, legit, "" )) {
    *ret = (uint) x;
  }
  return update_allgood (legit);
}

  bool
ProtoconFile::eval_gtz(uint* ret, Sesp sp)
{
  int x = 0;
  bool legit = eval_int (&x, sp);
  if (LegitCk( x > 0, legit, "" )) {
    *ret = (uint) x;
  }
  return update_allgood (legit);
}

  bool
ProtoconFile::eval_vbl(Xn::Vbl** ret, Sesp a)
{
  Claim( eq_cstr ("aref", ccstr_of_Sesp (car_of_Sesp (a))) );
  return eval_vbl(ret, cadr_of_Sesp (a), caddr_of_Sesp (a));
}

  bool
ProtoconFile::eval_vbl(Xn::Vbl** ret, Sesp b, Sesp c)
{
  Sign good = 1;

  DoLegit( good, "null variable or index?!" )
    good = b && c;

  const char* name = 0;
  DoLegit( good, "variable needs name" )
  {
    name = ccstr_of_Sesp (b);
    good = !!name;
  }

  const Xn::VblSymm* symm = 0;
  DoLegit( good, "variable lookup" )
  {
    const Xn::VblSymm** tmp = vbl_map.lookup(name);
    good = !!tmp;
    if (tmp)
      symm = *tmp;
  }

  int idx = 0;
  DoLegit( good, "eval array index" )
    good = eval_int(&idx, c);

  DoLegit( good, "" )
    *ret = symm->membs[umod_int (idx, symm->membs.sz())];

  DoLegit( good, "process needs read access to variable" ) {
    if ((bool)pc_symm) {
      const int* pcidx = index_map.lookup(pc_symm_spec->idx_name);
      if (pcidx) {
        const Xn::Pc& pc = *pc_symm->membs[*pcidx];
        bool found = false;
        for (uint i = 0; !found && i < pc.rvbls.sz(); ++i) {
          found = (pc.rvbls[i] == *ret);
        }
        good = found;
      }
    }
  }

  if (!good)
    *ret = 0;
  return update_allgood (good);
}

  bool
ProtoconFile::lookup_pfmla(Cx::PFmla* ret, const Cx::String& name)
{
  const Cx::PFmla* pf = sys->predicate_map.lookup(name);
  if (pf) {
    *ret = *pf;
    return true;
  }
  if ((bool)pc_symm) {
    const int* pcidx = index_map.lookup(pc_symm_spec->idx_name);
    if (pcidx) {
      Xn::NatPredicateMap* vals = pc_symm->predicate_map.lookup(name);
      if (vals) {
        *ret = vals->eval(*pcidx);
        return true;
      }
    }
  }
  return update_allgood (false);
}

  bool
ProtoconFile::lookup_int(int* ret, const Cx::String& name)
{
  const int* val = index_map.lookup(name);
  if (val) {
    *ret = *val;
    return true;
  }

  if (spec->constant_map.key_ck(name)) {
    *ret = spec->constant_map.lookup(name)->membs[0];
    return true;
  }
  if ((bool)pc_symm) {
    const int* pcidx = index_map.lookup(pc_symm_spec->idx_name);
    if (pcidx) {
      Xn::NatMap* vals = pc_symm_spec->let_map.lookup(name);
      if (vals) {
        *ret = vals->eval(*pcidx);
        return true;
      }
    }
  }
  return update_allgood (false);
}

