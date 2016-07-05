

#include "prot-xfile.hh"
#include "cx/bittable.hh"

#include "namespace.hh"

  bool
ProtoconFile::update_allgood(bool good)
{
  if (!allgood)  return false;
  if (good)  return true;
  allgood = false;
  DBog1( "Something terribly wrong at/after line:%u", this->text_nlines+1 );
  return false;
}

  void
ProtoconFile::bad_parse(const char* text, const char* reason)
{
  OFile ofile(stderr_OFile ());
  ofile << "Error at" << (text ? "" : "/after") << " line " << (this->text_nlines+1);
  if (text) {
     ofile << " in text: " << text;
  }
  if (reason) {
    ofile << "\nReason for error: " << reason;
  }
  ofile << ofile.endl();
  this->allgood = false;
}

  bool
ProtoconFile::add_variables(Sesp vbl_name_sp, Sesp vbl_nmembs_sp, Sesp vbl_dom_sp,
                            Xn::Vbl::ShadowPuppetRole role)
{
  if (!allgood)  return false;
  DeclLegit( good );
  const char* name = 0;
  uint nmembs = 0;
  uint domsz = 0;

  DoLegitLineP(name, "")
    ccstr_of_Sesp (vbl_name_sp);
  DoLegitLine("Domain of variable index strange.")
    eq_cstr ("NatDom", ccstr_of_Sesp (car_of_Sesp (vbl_nmembs_sp)));
  DoLegitLine("Domain of variable is strange.")
    eq_cstr ("NatDom", ccstr_of_Sesp (car_of_Sesp (vbl_dom_sp)));

  DoLegitLine( "" )
    eval_gtz (&nmembs, cadr_of_Sesp (vbl_nmembs_sp));

  DoLegitLine( "" )
    eval_gtz (&domsz, cadr_of_Sesp (vbl_dom_sp));

  DoLegit(0)
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
ProtoconFile::add_processes(Sesp pc_name, Sesp idx_name, Sesp npcs, Sesp map_vbl, Sesp map_expr)
{
  if (!allgood)  return false;
  Claim2( index_map.sz() ,==, 0 );
  DeclLegit( good );
  const char* name_a;
  const char* name_b;

  DoLegitLineP( name_a, 0 )
    ccstr_of_Sesp (pc_name);
  DoLegitLineP( name_b, 0 )
    ccstr_of_Sesp (idx_name);

  uint domsz = 0;
  DoLegitLine( "" )
    eval_nat (&domsz, cadr_of_Sesp (npcs));

  DoLegit( 0 ) {
    this->pc_symm =
      sys->topology.add_processes(name_a, name_b, (uint) domsz);
    this->pc_symm_spec = pc_symm->spec;
    pc_symm_spec->nmembs_expression = "";
    good = string_expression (pc_symm_spec->nmembs_expression, cadr_of_Sesp (npcs));
  }

  if (!nil_ck_Sesp (map_vbl)) {
    DoLegitLine( 0 )
      string_expression (pc_symm_spec->idxmap_name, map_vbl);
    DoLegitLine( 0 )
      string_expression (pc_symm_spec->idxmap_expression, map_expr);

    for (uint pcidx = 0; pcidx < pc_symm->membs.sz(); ++pcidx) {
      index_map[pc_symm_spec->idxmap_name] = pcidx;
      DoLegitLine( "evaluating process index map" )
        eval_int (&pc_symm->mapped_indices.membs[pcidx], map_expr);
    }
    index_map.erase(pc_symm_spec->idxmap_name);
  }
  return update_allgood (good);
}

  bool
ProtoconFile::add_constant(Sesp name_sp, Sesp val_sp)
{
  if (!allgood)  return false;
  DeclLegit( good );

  const char* name;
  DoLegitLineP( name, "" )
    ccstr_of_Sesp (name_sp);
  Xn::NatMap val(1);
  DoLegitLine("evaluating int")
    eval_int (&val.membs[0], val_sp);
  DoLegitLine( "finding expression" )
    string_expression (val.expression, val_sp);
  DoLegit(0)
    if (!spec->constant_map.key_ck(name))
      spec->constant_map.add(name, val);

  return update_allgood (good);
}

  bool
ProtoconFile::add_constant_list(Sesp name_sp, Sesp list_sp)
{
  if (!allgood)  return false;
  DeclLegit( good );

  const char* name;
  DoLegitLineP( name, "" )
    ccstr_of_Sesp (name_sp);

  Sesp a = list_sp;
  Claim( eq_cstr ("list", ccstr_of_Sesp (car_of_Sesp (a))) );
  Table<Sesp> membs;

  while (a = cdr_of_Sesp (a),
         !nil_ck_Sesp (a))
  {
    membs << car_of_Sesp (a);
  }

  Xn::NatMap val( membs.sz() );
  for (uint i = 0; i < membs.sz(); ++i) {
    DoLegitLine("evaluating int")
      eval_int (&val.membs[i], membs[i]);
  }

  DoLegitLine( "finding expression" )
    string_expression (val.expression, list_sp);
  DoLegit(0)
    if (!spec->constant_map.key_ck(name))
      spec->constant_map.add(name, val);

  return update_allgood (good);
}

  bool
ProtoconFile::add_let(Sesp name_sp, Sesp val_sp)
{
  if (!allgood)  return false;
  DeclLegit( good );
  const char* name;
  DoLegitLineP( name, "" )
    ccstr_of_Sesp (name_sp);

  Xn::NatMap let_vals( pc_symm->membs.sz() );
  for (uint i = 0; good && i < pc_symm->membs.sz(); ++i) {
    within_process(i);
    DoLegitLine( "" )
      eval_int (&let_vals.membs[i], val_sp);
  }
  escape_process();
  DoLegitLine( "finding expression" )
    string_expression (let_vals.expression, val_sp);
  DoLegit(0)
    pc_symm_spec->let_map.add(name, let_vals);
  return update_allgood (good);
}

  bool
ProtoconFile::add_scope_let(Sesp name_sp, Sesp val_sp)
{
  if (!allgood)  return false;
  DeclLegit( good );
  const char* name;
  DoLegitLineP( name, "" )
    ccstr_of_Sesp (name_sp);

  DoLegit(0)
    scope_let_map[name] = val_sp;

  return update_allgood (good);
}

  void
ProtoconFile::del_scope_let(Sesp name_sp)
{
  scope_let_map.erase(ccstr_of_Sesp(name_sp));
}

  bool
ProtoconFile::add_access(Sesp vbl_sp, Bit write, Bit random)
{
  if (!allgood)  return false;
  DeclLegit( good );
  const char* vbl_name = 0;
  Sesp vbl_idx_sp = 0;
  Xn::Net& topo = sys->topology;
  const Xn::VblSymm* vbl_symm = 0;

  // (aref vbl_name vbl_idx)
  DoLegitLineP( vbl_name, "" )
    ccstr_of_Sesp (cadr_of_Sesp (vbl_sp));

  DoLegitP( vbl_symm, "" )
  {
    const Xn::VblSymm** tmp = 0;
    tmp = vbl_map.lookup(vbl_name);
    if (tmp)  vbl_symm = *tmp;
  }

  DoLegit(0)
    vbl_idx_sp = caddr_of_Sesp (vbl_sp);

  DoLegitLine("")
    topo.pc_symms.sz() > 0;

  DoLegit("")
  {
    Xn::NatMap indices( pc_symm->membs.sz() );

    for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
      within_process(i);
      DoLegitLine("")
        eval_int (&indices.membs[i], vbl_idx_sp);
    }
    escape_process();

    DoLegitLine( "string_expression()" )
      string_expression(indices.expression, vbl_idx_sp);

    if (good) {
      if (write) {
        topo.add_write_access(+pc_symm, vbl_symm, indices);
        if (random) {
          pc_symm_spec->random_write_flags.top() = 1;
        }
      }
      else {
        topo.add_read_access(+pc_symm, vbl_symm, indices);
        if (random) {
          pc_symm_spec->random_read_flags.top() = 1;
          for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
            uint vidx = topo.vbls.index_of(pc_symm->membs[i]->rvbls.top());
            topo.vbls[vidx].random_flag = true;
          }
          DoLegitLine( "Can only 'random read' with puppet variables!" )
            pc_symm->rvbl_symms.top()->pure_puppet_ck();
        }
      }
    }
  }

  return update_allgood (good);
}

  bool
ProtoconFile::add_symmetric_links(Sesp let_names_sp, Sesp let_vals_list_sp)
{
  if (!allgood)  return false;
  DeclLegit( good );
  pc_symm_spec->link_symmetries.push(Xn::LinkSymmetry(sz_of_Sesp (let_vals_list_sp)));
  Xn::LinkSymmetry& link_symmetry = pc_symm_spec->link_symmetries.top();
  if (sz_of_Sesp (let_names_sp) == 1) {
    link_symmetry.let_expression = ccstr_of_Sesp (car_of_Sesp (let_names_sp));
    Sesp let_vals_sp = let_vals_list_sp;
    while (!nil_ck_Sesp (let_vals_sp)) {
      link_symmetry.multiset_expression.push_delim("", ", ");
      String val_expression;
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

    String tuple_expression;
    Sesp let_val_sp = car_of_Sesp (let_vals_sp);
    while (!nil_ck_Sesp (let_val_sp)) {
      tuple_expression.push_delim("(", ", ");

      String val_expression;
      DoLegitLine( "" )
        string_expression(val_expression, car_of_Sesp (let_val_sp));
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
                                   Sesp vbls_sp, Bit write, Bit random)
{
  if (!allgood)  return false;
  DeclLegit( good );
  Xn::LinkSymmetry& link_symmetry = pc_symm_spec->link_symmetries.top();

  while (!nil_ck_Sesp (vbls_sp)) {
    Sesp let_vals_sp = let_vals_list_sp;
    Table<uint> vbl_idcs;
    while (!nil_ck_Sesp (let_vals_sp)) {
      Sesp let_name_sp = let_names_sp;
      Sesp let_val_sp = car_of_Sesp (let_vals_sp);
      while (good && !nil_ck_Sesp (let_name_sp)) {
        DoLegitLine( "Tuple must be of the same size!" )
          !nil_ck_Sesp (let_val_sp);
        if (!good)  break;

        add_scope_let(car_of_Sesp (let_name_sp), car_of_Sesp (let_val_sp));
        let_name_sp = cdr_of_Sesp (let_name_sp);
        let_val_sp = cdr_of_Sesp (let_val_sp);
      }
      DoLegitLine( "Tuples must be of the same size!" )
        nil_ck_Sesp (let_val_sp);
      if (!good)  break;

      vbl_idcs.push(pc_symm_spec->rvbl_symms.sz());
      add_access(car_of_Sesp (vbls_sp), write, random);

      let_name_sp = let_names_sp;
      while (!nil_ck_Sesp (let_name_sp)) {
        del_scope_let(car_of_Sesp (let_name_sp));
        let_name_sp = cdr_of_Sesp (let_name_sp);
      }
      let_vals_sp = cdr_of_Sesp (let_vals_sp);
    }
    if (!good)  break;

    String index_expression;
    string_expression(index_expression, caddar_of_Sesp (vbls_sp));
    link_symmetry.add_link_symmetry(vbl_idcs, index_expression);
    vbls_sp = cdr_of_Sesp (vbls_sp);
  }
  return update_allgood (good);
}

  bool
ProtoconFile::parse_action(X::Fmla& act_xn, uint pcidx, Sesp act_sp,
                           bool auto_iden, Xn::Vbl::ShadowPuppetRole role)
{
  DeclLegit( good );
  const Xn::Net& topo = sys->topology;
  const Xn::Pc& pc = *pc_symm->membs[pcidx];

  const bool actto_op =
    eq_cstr ("-=>", ccstr_of_Sesp (car_of_Sesp (act_sp)));

  act_xn = false;
  within_process(pcidx);
  P::Fmla guard_pf;
  DoLegitLine( "eval guard" )
    eval(guard_pf, cadr_of_Sesp (act_sp));
  if (!good)  return false;

  P::Fmla assign_pf( true );

  BitTable wvbl_assigned( pc.wvbls.sz(), 0 );
  BitTable wvbl_randomized( pc.wvbls.sz(), 0 );

  bool all_wild = false;
  for (Sesp assign_sp = cddr_of_Sesp (act_sp);
       !nil_ck_Sesp (assign_sp);
       assign_sp = cdr_of_Sesp (assign_sp))
  {
    Sesp sp = car_of_Sesp (assign_sp);
    Claim( list_ck_Sesp (sp) );

    if (eq_cstr ("wild", ccstr_of_Sesp (car_of_Sesp (sp)))) {
      auto_iden = true;
      continue;
    }
    Claim( eq_cstr (":=", ccstr_of_Sesp (car_of_Sesp (sp))) );

    Sesp vbl_sp = cadr_of_Sesp (sp);
    Sesp val_sp = caddr_of_Sesp (sp);

    if (eq_cstr ("wild", ccstr_of_Sesp (car_of_Sesp (vbl_sp)))) {
      Claim( eq_cstr ("wild", ccstr_of_Sesp (car_of_Sesp (val_sp))) );
      all_wild = true;
      continue;
    }

    Xn::Vbl* vbl = 0;
    IntPFmla val;

    DoLegit( "lookup variable" ) {
      Claim( eq_cstr ("aref", ccstr_of_Sesp (car_of_Sesp (vbl_sp))) );
      const char* name = ccstr_of_Sesp (cadr_of_Sesp (vbl_sp));
      good = lookup_vbl(&vbl, name, caddr_of_Sesp (vbl_sp));
    }

    bool wild = false;
    DoLegit( "eval value" )
    {
      if (list_ck_Sesp(val_sp) && eq_cstr ("wild", ccstr_of_Sesp (car_of_Sesp (val_sp)))) {
        wild = true;
      }
      else {
        good = eval(val, val_sp);
      }
    }

    DoLegit( "non-writable variable in assignment" )
    {
      bool found = false;
      for (uint i = 0; i < pc.wvbls.sz(); ++i) {
        if (pc.wvbls[i] == vbl) {
          found = true;
          wvbl_assigned[i] = 1;
          if (wild) {
            wvbl_randomized[i] = 1;
          }
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
      const PFmlaVbl& pf_vbl = topo.pfmla_vbl(*vbl);
      val %= vbl->symm->domsz;
      assign_pf &= pf_vbl.img_eq(val);
    }

  }

  for (uint i = 0; i < pc.wvbls.sz(); ++i) {
    if (all_wild) {
      wvbl_assigned[i] = 1;
      wvbl_randomized[i] = 1;
    }
    else if (actto_op) {
      // The {-=>} operator automatically randomizes values.
      if (pc_symm_spec->random_write_flags[pc_symm->wmap[i]]) {
        if (!wvbl_assigned[i]) {
          wvbl_assigned[i] = 1;
          wvbl_randomized[i] = 1;
        }
      }
    }
    if (!auto_iden || wvbl_assigned[i]) {
      continue;
    }
    const PFmlaVbl& pf_vbl = topo.pfmla_vbl(*pc.wvbls[i]);
    assign_pf &= pf_vbl.img_eq(pf_vbl);
  }

  act_xn = guard_pf & assign_pf;

  // Smooth the 'random read' variables that are allowed by
  // this action's guard to make the action nondeterministic,
  // rather than having a unique action for every readable state.
  for (uint i = 0; i < pc.rvbls.sz(); ++i) {
    const Xn::Vbl& vbl = *pc.rvbls[i];
    if (!vbl.random_ck())
      continue;
    const PFmlaVbl& pfmla_vbl = topo.pfmla_vbl(vbl);
    act_xn = guard_pf & act_xn.smooth_pre(pfmla_vbl);
  }

  // Remove this action's cycles when -=> is used.
  // This is mostly just self-loops.
  if (actto_op) {
    X::Fmla pc_xn = act_xn;
    if (role == Xn::Vbl::Shadow)
      pc_xn = topo.proj_shadow(pc_xn);
    else
      pc_xn = topo.proj_puppet(pc_xn);

    Table<bool> changing(pc_symm->rvbl_symms.sz());
    for (uint i = 0; i < pc_symm->rvbl_symms.sz(); ++i) {
      changing[i] =
        pc_symm->write_flags[i]
        || pc.rvbls[i]->random_ck()
        || (role == Xn::Vbl::Shadow && pc_symm->rvbl_symms[i]->pure_puppet_ck())
        || (role != Xn::Vbl::Shadow && pc_symm->rvbl_symms[i]->pure_shadow_ck())
        ;
    }
    for (uint i = 0; i < pc_symm->rvbl_symms.sz(); ++i) {
      if (changing[i])  continue;
      const PFmlaVbl& pfmla_vbl = topo.pfmla_vbl(*pc.rvbls[i]);
      pc_xn &= pfmla_vbl.img_eq(pfmla_vbl);
    }

    P::Fmla scc;
    if (pc_xn.cycle_ck(&scc)) {
      X::Fmla self_xn = pc_xn & scc.cross(scc);
      for (uint i = 0; i < pc_symm->rvbl_symms.sz(); ++i) {
        if (changing[i])  continue;
        const PFmlaVbl& pfmla_vbl = topo.pfmla_vbl(*pc.rvbls[i]);
        self_xn = self_xn.smooth_img(pfmla_vbl);
      }
      act_xn -= self_xn;
    }
  }

  // Strictly remove self-loops when pure shadow variables exist.
  if (pc_symm->pure_shadow_ck()) {
    X::Fmla self_xn( true );
    for (uint i = 0; i < pc.wvbls.sz(); ++i) {
      const PFmlaVbl& pf_vbl = topo.pfmla_vbl(*pc.wvbls[i]);
      self_xn &= pf_vbl.img_eq(pf_vbl);
    }
    act_xn -= self_xn;
  }

  if (good)
    escape_process();
  return update_allgood (good);
}

  bool
ProtoconFile::parse_action(X::Fmla& act_pf, Table<X::Fmla>& pc_xns, Sesp act_sp,
                           bool auto_iden, Xn::Vbl::ShadowPuppetRole role)
{
  if (!allgood)  return false;
  DeclLegit( good );
  Claim( pc_symm );
  act_pf = false;
  pc_xns.resize(pc_symm->membs.sz());

  for (uint pcidx = 0; good && pcidx < pc_symm->membs.sz(); ++pcidx) {
    DoLegitLine( "parse action" )
      parse_action(pc_xns[pcidx], pcidx, act_sp, auto_iden, role);
    if (good)
      act_pf |= pc_xns[pcidx] & pc_symm->membs[pcidx]->act_unchanged_pfmla;
  }
  return update_allgood (good);
}

  bool
ProtoconFile::add_action(Sesp act_sp, Xn::Vbl::ShadowPuppetRole role)
{
  if (!allgood)  return false;
  DeclLegit( good );
  Claim( pc_symm );
  Xn::Net& topo = sys->topology;

  DoLegit( "" )
  {
    if (role != Xn::Vbl::Puppet) {
      String act_expression;
      good = string_expression (act_expression, act_sp);
      if (good) {
        pc_symm_spec->shadow_act_strings.push(act_expression);
      }
    }
  }

  if (!this->interpret_ck())  return update_allgood (good);

  X::Fmla act_pf( false );
  Table<X::Fmla> pc_xns;
  DoLegitLine( "parse action" )
    parse_action(act_pf, pc_xns, act_sp, true, role);

  if (good) {
    for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
      if (role != Xn::Vbl::Puppet) {
        pc_symm->membs[i]->shadow_xn |= topo.proj_shadow(pc_xns[i]);
      }
      if (role != Xn::Vbl::Shadow) {
        pc_symm->membs[i]->puppet_xn |= pc_xns[i];
      }
    }
  }

  if (false)
  DoLegitLine("self-loop")
    !act_pf.overlap_ck(topo.identity_xn);

  DoLegit("")
  {
    if (role != Xn::Vbl::Puppet) {
      const X::Fmla& shadow_act_pf =
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
  if (!allgood)  return false;
  DeclLegit( good );
  Claim( pc_symm );

  DoLegit( "" )
  {
    String act_expression;
    good = string_expression (act_expression, act_sp);
    if (good) {
      pc_symm_spec->forbid_act_strings.push(act_expression);
    }
  }

  if (!this->interpret_ck())  return update_allgood (good);

  X::Fmla act_pf( false );
  Table<X::Fmla> pc_xns;
  DoLegitLine( "parse action" )
    parse_action(act_pf, pc_xns, act_sp, false, Xn::Vbl::Puppet);

  DoLegit( "" ) {
    for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
      pc_symm->membs[i]->forbid_xn |= pc_xns[i];
    }
  }

  return update_allgood (good);
}

  bool
ProtoconFile::permit_action(Sesp act_sp)
{
  if (!allgood)  return false;
  DeclLegit( good );
  Claim( pc_symm );

  DoLegit( "" )
  {
    String act_expression;
    good = string_expression (act_expression, act_sp);
    if (good) {
      pc_symm_spec->permit_act_strings.push(act_expression);
    }
  }

  if (!this->interpret_ck())  return update_allgood (good);

  X::Fmla act_pf( false );
  Table<X::Fmla> pc_xns;
  DoLegitLine( "parse action" )
    parse_action(act_pf, pc_xns, act_sp, false, Xn::Vbl::Puppet);

  DoLegit( "" ) {
    for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
      pc_symm->membs[i]->permit_xn |= pc_xns[i];
    }
  }

  return update_allgood (good);
}

  bool
ProtoconFile::conflict_action(Sesp act_sp)
{
  if (!allgood)  return false;
  Xn::Net& topo = sys->topology;

  uint rep_pcidx = 0;
  if (!pc_symm->representative(&rep_pcidx))
    return true;

  DeclLegit( good );

  X::Fmla xn;
  DoLegitLine( "parse action" )
    parse_action(xn, rep_pcidx, act_sp, true, Xn::Vbl::Puppet);

  const Xn::Pc& pc = *pc_symm->membs[rep_pcidx];
  Xn::ActSymm act;
  act.pc_symm = +pc_symm;
  act.vals.affysz(pc.rvbls.sz() + pc.wvbls.sz());

  for (uint i = 0; good && i < pc.rvbls.sz(); ++i) {
    if (pc_symm->rvbl_symms[i]->pure_shadow_ck()) {
      act.vals[i] = 0;
      continue;
    }

    Table<uint> rvbl_indices(1);
    rvbl_indices[0] = pc.rvbls[i]->pfmla_idx;
    uint val;
    xn.state(&val, rvbl_indices);
    act.vals[i] = val;

    const PFmlaVbl& pf_vbl = topo.pfmla_vbl(*pc.rvbls[i]);
    DoLegitLine( "Conflict action not unique." )
      xn.subseteq_ck(pf_vbl == val);
  }

  for (uint i = 0; good && i < pc.wvbls.sz(); ++i) {
    const PFmlaVbl& pf_vbl = topo.pfmla_vbl(*pc.wvbls[i]);
    if (pc_symm->wvbl_symms[i]->pure_shadow_ck()) {
      if (xn.subseteq_ck(pf_vbl.img_eq(pf_vbl))) {
        act.vals[pc.rvbls.sz() + i] = pc_symm->wvbl_symms[i]->domsz;
        continue;
      }
    }

    Table<uint> wvbl_indices(1);
    wvbl_indices[0] = pc.wvbls[i]->pfmla_idx;
    uint val;
    xn.img().state(&val, wvbl_indices);
    act.vals[pc.rvbls.sz() + i] = val;

    DoLegitLine( "Conflict action not unique." )
      xn.subseteq_ck(pf_vbl.img_eq(val));
  }
  if (good) {
    conflict << act;
  }

  return update_allgood (good);
}

  bool
ProtoconFile::push_conflict_action()
{
  if (!allgood)  return false;
  if (conflict.size() == 0)  return true;
  pc_symm->conflicts << FlatSet<Xn::ActSymm>(conflict);
  conflict.clear();
  return update_allgood (true);
}

  bool
ProtoconFile::add_pc_predicate(Sesp name_sp, Sesp val_sp)
{
  if (!allgood)  return false;
  DeclLegit( good );

  if (!this->interpret_ck())  return update_allgood (good);

  const char* name;
  DoLegitLineP( name, "" )
    ccstr_of_Sesp (name_sp);

  Xn::NatPredicateMap let_vals( pc_symm->membs.sz() );
  for (uint i = 0; good && i < pc_symm->membs.sz(); ++i) {
    within_process(i);
    DoLegitLine( "" )
      eval (let_vals.membs[i], val_sp);
  }
  escape_process();

  DoLegitLine( "finding expression" )
    string_expression (let_vals.expression, val_sp);
  DoLegit( "" )
    pc_symm->predicate_map.add(name, let_vals);
  return update_allgood (good);
}

  bool
ProtoconFile::add_pc_assume(Sesp assume_sp)
{
  if (!allgood)  return false;
  DeclLegit( good );

  String assume_expression;
  DoLegitLine( "" )
    parend_string_expression(assume_expression, assume_sp);

  DoLegit( "" ) {
    if (!pc_symm_spec->closed_assume_expression.empty_ck()) {
      pc_symm_spec->closed_assume_expression << " && ";
    }
    pc_symm_spec->closed_assume_expression << assume_expression;
  }

  if (!this->interpret_ck())  return update_allgood (good);

  P::Fmla pf;

  for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
    within_process(i);
    DoLegitLine( "" )
      eval(pf, assume_sp);

    if (!good)  break;
    pc_symm->membs[i]->closed_assume &= pf;
    sys->closed_assume &= pf;
  }

  escape_process();
  return update_allgood (good);
}

  bool
ProtoconFile::add_pc_legit(Sesp legit_sp)
{
  if (!allgood)  return false;
  DeclLegit( good );

  String invariant_expression;
  DoLegitLine( "" )
    string_expression(invariant_expression, legit_sp);

  DoLegit( "" )
  {
    if (!pc_symm_spec->invariant_expression.empty_ck()) {
      pc_symm_spec->invariant_expression =
        String("(") + pc_symm_spec->invariant_expression + ") && ";
    }
    pc_symm_spec->invariant_expression += invariant_expression;
  }

  if (!this->interpret_ck())  return update_allgood (good);

  P::Fmla pf;

  for (uint i = 0; i < pc_symm->membs.sz(); ++i) {
    within_process(i);
    DoLegitLine( "" )
      eval(pf, legit_sp);

    DoLegit( "" )
    {
      sys->invariant &= pf;
      pc_symm->membs[i]->invariant &= pf;
    }
  }

  escape_process();
  return update_allgood (good);
}

  bool
ProtoconFile::finish_pc_def()
{
  this->pc_symm = 0;
  this->pc_symm_spec = 0;
  return update_allgood (true);
}

  bool
ProtoconFile::add_predicate(Sesp name_sp, Sesp val_sp)
{
  if (!allgood)  return false;
  DeclLegit( good );
  const char* name;

  DoLegitLineP( name, "" )
    ccstr_of_Sesp (name_sp);

  String expression;
  DoLegitLine( "finding expression" )
    string_expression (expression, val_sp);


  P::Fmla pf(false);
  if (this->interpret_ck()) {
    DoLegitLine( 0 )
      eval(pf, val_sp);
  }

  DoLegit( 0 )
    sys->predicate_map.add(name, pf, expression);

  return update_allgood (good);
}

  bool
ProtoconFile::add_assume(Sesp assume_sp)
{
  if (!allgood)  return false;
  DeclLegit( good );

  String str;
  DoLegitLine( "convert invariant expression to string" )
    parend_string_expression(str, assume_sp);

  DoLegit(0) {
    if (spec->closed_assume_expression != "") {
      spec->closed_assume_expression << "\n  &&\n  ";
    }
    spec->closed_assume_expression << str;
  }
  if (!this->interpret_ck())  return update_allgood (good);

  P::Fmla pf;
  DoLegitLine( "parse invariant" )
    eval(pf, assume_sp);

  DoLegit(0)
    sys->closed_assume &= pf;

  return update_allgood (good);
}

  bool
ProtoconFile::assign_legit_mode(Xn::InvariantStyle style, Xn::InvariantScope scope)
{
  if (!allgood)  return false;
  DeclLegit( good );
  if (legit_mode_assigned) {
    DoLegitLine( "Invariant must have the same style in all places." )
      (spec->invariant_style == style &&
       spec->invariant_scope == scope);
  }
  spec->invariant_style = style;
  spec->invariant_scope = scope;
  legit_mode_assigned = true;
  return update_allgood (good);
}

  bool
ProtoconFile::add_legit(Sesp legit_sp)
{
  if (!allgood)  return false;
  DeclLegit( good );

  String invariant_expression;
  DoLegitLine( "convert invariant expression to string" )
    string_expression(invariant_expression, legit_sp);

  DoLegit(0) {
    if (spec->invariant_expression != "") {
      spec->invariant_expression =
        String("(") + spec->invariant_expression + ")\n  &&\n  ";
    }
    spec->invariant_expression += invariant_expression;
  }
  if (!this->interpret_ck())  return update_allgood (good);


  P::Fmla pf;
  DoLegitLine( "parse invariant" )
    eval(pf, legit_sp);

  DoLegit(0)
    sys->invariant &= pf;

  return update_allgood (good);
}

  bool
ProtoconFile::string_expression(String& ss, Sesp a)
{
  if (!allgood)  return false;
  DeclLegit( good );

  const char* key = 0;

  DoLegitLine( "" )
    !!a;

  DoLegitP( key, "ccstr_of_Sesp()" )
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
           eq_cstr (key, "==>") ||
           eq_cstr (key, "<=>") ||
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
       eq_cstr (key, "==>") ||
       eq_cstr (key, "<=>"));
    string_expression (ss, cadr_of_Sesp (a));
    if (pad)  ss += " ";
    ss += key;
    if (pad)  ss += " ";
    string_expression (ss, caddr_of_Sesp (a));
  }
  else if (eq_cstr (key, "xor")) {
    string_expression (ss, cadr_of_Sesp (a));
    ss += "!=";
    string_expression (ss, caddr_of_Sesp (a));
  }
  else if (eq_cstr (key, "-->") ||
           eq_cstr (key, "-=>")) {
    string_expression (ss, cadr_of_Sesp (a));
    ss << " " << key;
    for (Sesp b = cddr_of_Sesp (a); !nil_ck_Sesp (b); b = cdr_of_Sesp (b)) {
      ss += " ";
      string_expression (ss, car_of_Sesp (b));
      ss += ";";
    }
  }
  else if (eq_cstr (key, "min") ||
           eq_cstr (key, "max")) {
    ss << key << "(";
    string_expression (ss, cadr_of_Sesp (a));
    ss << ",";
    string_expression (ss, caddr_of_Sesp (a));
    ss << ")";
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
    ss += " < ";
    Sesp b = caddr_of_Sesp (a);
    string_expression (ss, cadr_of_Sesp (b));
    ss += " : ";
    string_expression (ss, cadddr_of_Sesp (a));
  }
  else if (eq_cstr (key, "list")) {
    bool first = true;
    Sesp b = a;
    while (b = cdr_of_Sesp (b), !nil_ck_Sesp (b)) {
      if (first)  ss << '(';
      else        ss << ",";
      first = false;
      string_expression (ss, car_of_Sesp (b));
    }
    ss << ')';
  }
  else {
    good = false;
    DBog1( "No matching string, key is: \"%s\"", key );
  }

  return update_allgood (good);
}

  bool
ProtoconFile::parend_string_expression(String& ss, Sesp a)
{
  const char* key = 0;
  if (list_ck_Sesp (a)) {
    key = ccstr_of_Sesp (car_of_Sesp (a));
  }
  bool wrap = (!eq_cstr (key, "(bool)") &&
               !eq_cstr (key, "(int)"));
  if (wrap)  ss << '(';
  DeclLegit( good );
  DoLegitLine( "" )
    good = string_expression(ss, a);
  if (wrap)  ss << ')';
  return good;
}

  bool
ProtoconFile::eval(P::Fmla& pf, Sesp a)
{
  if (!allgood)  return false;
  DeclLegit( good );

  DoLegitLine("")
    !!a;

  DoLegit(0) {
    const char* name = ccstr_of_Sesp (a);
    if (name)
    {
      good = lookup_pfmla(&pf, name);
      if (!good)
        bad_parse(name, "Unknown predicate name.");
      return update_allgood(good);
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
  IntPFmla ipf_b;
  IntPFmla ipf_c;
  P::Fmla pf_b;
  P::Fmla pf_c;

  //DBog1("key is: %s", key);

  if (eq_cstr (key, "(bool)") ||
      eq_cstr (key, "(int)" ))
  {
    DoLegitLine("")
      eval(pf, b);
  }
  else if (eq_cstr (key, "!")) {
    DoLegitLine("")
      eval(pf, b);
    DoLegit(0)
      pf = !pf;
  }
  else if (eq_cstr (key, "&&")) {
    DoLegitLine("")
      eval(pf, b);

    DoLegit(0) {
      if (!pf.sat_ck()) {
        // Short circuit.
      }
      else {
        DoLegitLine("")
          eval(pf_c, c);
        if (good)
          pf &= pf_c;
      }
    }
  }
  else if (eq_cstr (key, "||")) {
    DoLegitLine("")
      eval(pf, b);

    DoLegit(0) {
      if (pf.tautology_ck()) {
        // Short circuit.
      }
      else {
        DoLegitLine("")
          eval(pf_c, c);
        if (good)
          pf |= pf_c;
      }
    }
  }
  else if (eq_cstr (key, "==>")) {
    DoLegitLine("")
      eval(pf, b);
    DoLegit(0) {
      if (!pf.sat_ck()) {
        // Short circuit.
        pf = true;
      }
      else {
        DoLegitLine("")
          eval(pf_c, c);
        if (good)
          pf = ~pf | pf_c;
      }
    }
  }
  else if (eq_cstr (key, "<=>") ||
           eq_cstr (key, "xor")
          )
  {
    DoLegitLine("")
      eval(pf, b);
    DoLegitLine("")
      eval(pf_c, c);

    if (!good)
      /* Nothing.*/;
    else if (eq_cstr (key, "<=>"))
      pf.defeq_xnor(pf_c);
    else if (eq_cstr (key, "xor"))
      pf ^= pf_c;
    else
      Claim( 0 && "Missing case." );
  }
  else if (eq_cstr (key, "<" ) ||
           eq_cstr (key, "<=") ||
           eq_cstr (key, "!=") ||
           eq_cstr (key, "==") ||
           eq_cstr (key, ">=") ||
           eq_cstr (key, ">" ))
  {
    DoLegitLine("")
      eval(ipf_b, b);
    DoLegitLine("")
      eval(ipf_c, c);

    DoLegit(0) {
      if      (eq_cstr (key, "<" ))  pf = (ipf_b < ipf_c);
      else if (eq_cstr (key, "<="))  pf = (ipf_b <= ipf_c);
      else if (eq_cstr (key, "!="))  pf = (ipf_b != ipf_c);
      else if (eq_cstr (key, "=="))  pf = (ipf_b == ipf_c);
      else if (eq_cstr (key, ">="))  pf = (ipf_b >= ipf_c);
      else if (eq_cstr (key, ">" ))  pf = (ipf_b > ipf_c);
      else Claim(0 && "Missing case.");
    }
  }
  else if (eq_cstr (key, "forall") ||
           eq_cstr (key, "exists") ||
           eq_cstr (key, "unique")
          )
  {
    const char* idxname = ccstr_of_Sesp (b);
    DoLegitLine("")
      !!idxname;
    DoLegitLine("")
      eval(ipf_c, c);
    DoLegitLine("")
      ipf_c.vbls.sz() == 0;

    DoLegit("") {
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
#if 1
      for (uint i = 0; good && i < n; ++i) {
        index_map[idxname] = ipf_c.state_map[i];
        DoLegitLine("")
          eval(pf_c, d);
        DoLegit("") {
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
#else
      Table< P::Fmla > pfmlas( n );

      for (uint i = 0; good && i < n; ++i) {
        index_map[idxname] = ipf_c.state_map[i];
        DoLegitLine("")
          eval(pfmlas[i], d);
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
            P::Fmla conj( pfmlas[i] );
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
#endif
    }
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
ProtoconFile::eval(IntPFmla& ipf, Sesp a)
{
  if (!allgood)  return false;
  DeclLegit( good );

  DoLegitLine( "" )
    !!a;

  DoLegit( "" )
  {
    const char* name = ccstr_of_Sesp (a);
    if (name)
    {
      Sesp* val_sp = scope_let_map.lookup(name);
      if (val_sp) {
        DoLegitLine( "evaluating scope'd let" )
          eval(ipf, *val_sp);
        return update_allgood (good);
      }

      int val = 0;
      DoLegitLine( "lookup_int()" )
        lookup_int(&val, name);

      DoLegit(0)
        ipf = IntPFmla( val );
      return update_allgood (good);
    }

    uint x = 0;
    if (uint_of_Sesp (a, &x)) {
      ipf = IntPFmla( x );
      //DBog1("int is: %u", x);
      return update_allgood (good);
    }
  }

  if (!good)
    return update_allgood (good);

  Sesp b = cdr_of_Sesp (a);
  Sesp c = cdr_of_Sesp (b);
  Sesp d = cdr_of_Sesp (c);

  a = car_of_Sesp (a);
  b = car_of_Sesp (b);
  c = car_of_Sesp (c);
  d = car_of_Sesp (d);

  const char* key = ccstr_of_Sesp (a);

  IntPFmla ipf_c;

  DoLegitLine("car_of_Sesp()")
    !!a;
  DoLegitLine("ccstr_of_Sesp()")
    !!key;

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
    DoLegitLine("")
      eval(ipf, b);
  }
  else if (eq_cstr (key, "negate")) {
    DoLegitLine("")
      eval(ipf, b);
    DoLegit(0)
      ipf.negate();
  }
  else if (eq_cstr (key, "+") ||
           eq_cstr (key, "-") ||
           eq_cstr (key, "*") ||
           eq_cstr (key, "/") ||
           eq_cstr (key, "%") ||
           eq_cstr (key, "^") ||
           eq_cstr (key, "min") ||
           eq_cstr (key, "max")
          ) {
    DoLegitLine("")
      eval(ipf, b);
    DoLegitLine("")
      eval(ipf_c, c);
    if (!good)
      /*Nothing*/;
    else if (eq_cstr (key, "+"))
      ipf += ipf_c;
    else if (eq_cstr (key, "-"))
      ipf -= ipf_c;
    else if (eq_cstr (key, "*"))
      ipf *= ipf_c;
    else if (eq_cstr (key, "/"))
      ipf /= ipf_c;
    else if (eq_cstr (key, "%"))
      ipf %= ipf_c;
    else if (eq_cstr (key, "^"))
      ipf.defeq_pow(ipf_c);
    else if (eq_cstr (key, "min"))
      ipf.defeq_min(ipf_c);
    else if (eq_cstr (key, "max"))
      ipf.defeq_max(ipf_c);
    else
      Claim(0 && "Missed a case!");
  }
  else if (eq_cstr (key, "NatDom")) {
    uint domsz = 0;
    DoLegitLine("")
      eval_gtz (&domsz, b);
    DoLegit(0)
      ipf = IntPFmla( 1, 0, domsz );
  }
  else if (eq_cstr (key, "iif")) {
    P::Fmla pf( true );
    DoLegitLine("")
      eval(pf, b);

    DoLegit("") {
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
    DoLegitLine("")
      eval(ipf, b);
  }
  else if (eq_cstr (key, "aref")) {
    DoLegitLine("")
      eval_vbl(&ipf, ccstr_of_Sesp (b), c);
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
  DeclLegit( good );
  IntPFmla ipf;
  DoLegitLine("")
    eval(ipf, sp);

  DoLegitLine("")
    ipf.state_map.sz() == 1;

  DoLegit(0)
    *ret = ipf.state_map[0];
  return update_allgood (good);
}

  bool
ProtoconFile::eval_nat(uint* ret, Sesp sp)
{
  int x = 0;
  DeclLegit( good );
  DoLegitLine("")
    eval_int (&x, sp);

  DoLegitLine("cannot be negative")
    x >= 0;

  DoLegit(0)
    *ret = (uint) x;
  return update_allgood (good);
}

  bool
ProtoconFile::eval_gtz(uint* ret, Sesp sp)
{
  int x = 0;
  DeclLegit( good );
  DoLegitLine("")
    eval_int (&x, sp);
  DoLegitLine("must be positive")
    x > 0;
  DoLegit(0)
    *ret = (uint) x;
  return update_allgood (good);
}

  bool
ProtoconFile::eval_vbl(IntPFmla* ret, const String& name, Sesp idx_sp)
{
  DeclLegit( good );

  const Xn::NatMap* tup = spec->constant_map.lookup(name);
  if (tup) {
    int idx = 0;
    DoLegitLine( "eval array index" )
      eval_int(&idx, idx_sp);
    if (good) {
      *ret = IntPFmla(tup->membs[umod_int (idx, tup->membs.sz())]);
    }
  }
  else {
    Xn::Vbl* vbl = 0;
    DoLegitLine( "" )
      lookup_vbl(&vbl, name, idx_sp);
    DoLegit(0)
      *ret = IntPFmla(sys->topology.pfmla_vbl(*vbl));
  }
  return update_allgood (good);
}

  void
ProtoconFile::within_process(uint pcidx)
{
  Claim( !!pc_symm );
  Claim( !!pc_symm_spec );
  index_map[pc_symm_spec->idx_name] = pc_symm->mapped_indices.eval(pcidx);
  pc_in_use = pc_symm->membs[pcidx];
}

  void
ProtoconFile::escape_process()
{
  Claim( !!pc_symm_spec );
  index_map.erase(pc_symm_spec->idx_name);
  pc_in_use = 0;
}

  bool
ProtoconFile::lookup_vbl(Xn::Vbl** ret, const String& name, Sesp idx_sp)
{
  DeclLegit( good );
  Claim( idx_sp && "null index expression" );

  int idx = 0;
  DoLegitLine( "eval array index" )
    eval_int(&idx, idx_sp);

  const Xn::VblSymm** tmp = vbl_map.lookup(name);
  if (!tmp)
    return false;

  const Xn::VblSymm* symm = *tmp;
  *ret = symm->membs[umod_int (idx, symm->membs.sz())];
  Claim( *ret );

  if (!pc_symm)
    return true;

  DoLegit( "process needs read access to variable" ) {
    if (!!pc_in_use) {
      const Xn::Pc& pc = *pc_in_use;
      bool found = false;
      for (uint i = 0; !found && i < pc.rvbls.sz(); ++i) {
        found = (pc.rvbls[i] == *ret);
      }
      good = found;
    }
  }

  if (!good)
    *ret = 0;
  return update_allgood (good);
}

  bool
ProtoconFile::lookup_pfmla(P::Fmla* ret, const String& name)
{
  if (name == "true") {
    *ret = true;
    return true;;
  }
  if (name == "false") {
    *ret = false;
    return true;;
  }
  const P::Fmla* pf = sys->predicate_map.lookup(name);
  if (pf) {
    *ret = *pf;
    return true;
  }
  if ((bool)pc_symm) {
    if (!!pc_in_use) {
      Xn::NatPredicateMap* vals = pc_symm->predicate_map.lookup(name);
      if (vals) {
        *ret = vals->eval(pc_in_use->symm_idx);
        return true;
      }
    }
  }

  bad_parse(name.ccstr(), "Unknown predicate name.");
  return false;
}

  bool
ProtoconFile::lookup_int(int* ret, const String& name)
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
  if ((bool)pc_symm && (bool)pc_in_use) {
    Xn::NatMap* vals = pc_symm_spec->let_map.lookup(name);
    if (vals) {
      *ret = vals->eval(pc_in_use->symm_idx);
      return true;
    }
  }
  return update_allgood (false);
}

}

