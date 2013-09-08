

#include "protoconfile.hh"

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
  }
  if (LegitCk( good, allgood, "" )) {}
  return good;
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
    if (LegitCk(eval_gtz (&domsz, cadr_of_Sesp (npcs)), good, "")) {
      sys->topology.add_processes(name_a, (uint) domsz);
    }
  }
  if (LegitCk( good, allgood, "" )) {}
  return good;
}

  bool
ProtoconFile::add_let(Sesp name_sp, Sesp val_sp)
{
  bool legit = true;
  const char* name = ccstr_of_Sesp (name_sp);
  if (LegitCk(name, legit, "")) {
    let_map[name] = val_sp;
  }
  if (LegitCk( legit, allgood, "" )) {}
  return legit;
}

  bool
ProtoconFile::add_access(Sesp vbl_sp, Sesp pc_idx_sp, Bit write)
{
  bool legit = true;
  const char* idx_name = 0;
  const char* vbl_name = 0;
  Sesp vbl_idx_sp = 0;
  Xn::Net& topo = sys->topology;
  const Xn::VblSymm* vbl_symm = 0;

  idx_name = ccstr_of_Sesp (pc_idx_sp);

  if (LegitCk( idx_name, legit, "" ))
  {
    // (aref vbl_name vbl_idx)
    vbl_name = ccstr_of_Sesp (cadr_of_Sesp (vbl_sp));
  }
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
    Xn::PcSymm& pc_symm = topo.pc_symms.top();
    Xn::NatMap indices( pc_symm.membs.sz() );

    for (uint i = 0; i < pc_symm.membs.sz(); ++i) {
      index_map[idx_name] = i;
      if (LegitCk( eval_int (&indices.membs[i], vbl_idx_sp), legit, "" )) {}
    }
    index_map.erase(idx_name);

    if (legit) {
      bool bstat = expression_chunks(indices.expression_chunks, vbl_idx_sp, idx_name);
      if (LegitCk(bstat, legit, "expression_chunks()"))
      {}
    }

    if (legit) {
      if (write) {
        topo.add_write_access(&pc_symm, vbl_symm, indices);
      }
      else {
        topo.add_read_access(&pc_symm, vbl_symm, indices);
      }
    }
  }

  if (LegitCk( legit, allgood, "" )) {}
  return legit;
}

  bool
ProtoconFile::add_action(Sesp act_sp, Sesp pc_idx_sp)
{
  bool legit = true;
  Xn::Net& topo = sys->topology;
  const char* idx_name = ccstr_of_Sesp (pc_idx_sp);
  if (LegitCk( idx_name, legit, "" ))
  {}
  if (LegitCk( topo.pc_symms.sz() > 0, legit, "" ))
  {
    Cx::PFmla act_pf( false );
    Xn::PcSymm& pc_symm = topo.pc_symms.top();

    for (uint i = 0; legit && i < pc_symm.membs.sz(); ++i) {
      Xn::Pc& pc = *pc_symm.membs[i];
      index_map[idx_name] = i;
      Cx::PFmla guard_pf;
      if (LegitCk( eval(guard_pf, cadr_of_Sesp (act_sp)), legit, "" ))
      {
        Cx::PFmla assign_pf( topo.identity_pfmla );
        Sesp assign_sp = cddr_of_Sesp (act_sp);

        for (uint j = 0; j < pc.wvbls.sz(); ++j) {
          const Xn::Vbl& vbl = *pc.wvbls[j];
          if (vbl.symm->pure_puppet_ck()) {
            assign_pf = assign_pf.smooth(topo.pfmla_vbl(vbl));
          }
        }

        while (!nil_ck_Sesp (assign_sp)) {
          Sesp sp = car_of_Sesp (assign_sp);
          Claim( eq_cstr (":=", ccstr_of_Sesp (car_of_Sesp (sp))) );
          Sesp vbl_sp = cadr_of_Sesp (sp);
          Sesp val_sp = caddr_of_Sesp (sp);
          assign_sp = cdr_of_Sesp (assign_sp);

          Xn::Vbl* vbl = 0;
          Cx::IntPFmla val;
          if (LegitCk( eval_vbl(&vbl, vbl_sp), legit, "" )) {}
          if (LegitCk( eval(val, val_sp), legit, "" )) {
            val %= vbl->symm->domsz;
            const Cx::PFmlaVbl& pf_vbl = topo.pfmla_vbl(*vbl);
            assign_pf = (assign_pf.smooth(pf_vbl)
                         && pf_vbl.img_eq(val));
          }
        }
        act_pf |= guard_pf & assign_pf;
      }
    }
    index_map.erase(idx_name);

    if (LegitCk( !act_pf.overlap_ck(topo.identity_pfmla), legit, "action has self-loop" )) {
      pc_symm.shadow_pfmla |= act_pf;
      sys->shadow_pfmla |= act_pf;

      const Cx::PFmla& pre_pf = act_pf.pre();
      const Cx::PFmla& img_pf = act_pf.img();
      bool fully_defined = true;

      for (uint i = 0; i < pc_symm.rvbl_symms.sz(); ++i) {
        const Xn::VblSymm& vbl_symm = *pc_symm.rvbl_symms[i];
        if (!vbl_symm.pure_puppet_ck())
          continue;
        if (!pre_pf.equiv_ck(pre_pf.smooth(vbl_symm.pfmla_list_id)))
          continue;

        if (pc_symm.write_flags[i]) {
          if (!img_pf.equiv_ck(img_pf.smooth(vbl_symm.pfmla_list_id)))
            continue;
        }

        fully_defined = false;
        break;
      }

      if (fully_defined) {
        pc_symm.direct_pfmla |= act_pf;
        sys->direct_pfmla |= act_pf;
      }
    }
  }
  if (LegitCk( legit, allgood, "" )) {}
  return legit;
}

  bool
ProtoconFile::add_legit(Sesp legit_sp, Sesp pc_idx_sp)
{
  bool good = true;
  Xn::Net& topo = sys->topology;
  const char* idx_name = ccstr_of_Sesp (pc_idx_sp);

  if (LegitCk( idx_name, good, "" ))
  {}
  if (LegitCk( topo.pc_symms.sz() > 0, good, "" ))
  {
    Xn::PcSymm& pc_symm = topo.pc_symms.top();
    Cx::PFmla pf;

    for (uint i = 0; i < pc_symm.membs.sz(); ++i) {
      index_map[idx_name] = i;
      if (LegitCk( eval(pf, legit_sp), good, "" ))
      {
        sys->invariant &= pf;
      }
    }
    Cx::String invariant_expression;
    if (LegitCk( expression(invariant_expression, legit_sp), good, "" )) {
      if (sys->invariant_expression != "") {
        sys->invariant_expression =
          Cx::String("(") + sys->invariant_expression + ")\n  &&\n  ";
      }

      sys->invariant_expression += Cx::String("(forall ")
        + idx_name + " <- Nat % " + pc_symm.membs.sz() + " : ";
      sys->invariant_expression += invariant_expression;;
      sys->invariant_expression += ")";
    }
    index_map.erase(idx_name);
  }
  if (LegitCk( good, allgood, "" )) {}
  return good;
}

  bool
ProtoconFile::add_legit(Sesp legit_sp)
{
  bool good = true;

  Cx::PFmla pf;
  if (LegitCk( eval(pf, legit_sp), good, "" ))
    sys->invariant &= pf;

  Cx::String invariant_expression;
  if (LegitCk( expression(invariant_expression, legit_sp), good, "" )) {
    if (sys->invariant_expression != "") {
      sys->invariant_expression =
        Cx::String("(") + sys->invariant_expression + ")\n  &&\n  ";
    }
    sys->invariant_expression += invariant_expression;;
  }

  if (LegitCk( good, allgood, "" )) {}
  return good;
}

  bool
ProtoconFile::expression(Cx::String& expression, Sesp a)
{
  Cx::Table<Cx::String> chunks(1);
  bool good = expression_chunks(chunks, a, "");
  Claim2( chunks.sz() ,==, 1 );
  expression = chunks[0];
  return good;
}

  bool
ProtoconFile::expression_chunks(Cx::Table<Cx::String>& chunks, Sesp a, const Cx::String& idx_name)
{
  if (chunks.sz() == 0) {
    chunks.push("");
  }

  bool good = true;

  const char* key = 0;

  if (LegitCk( a, good, "" )) {
    const char* name = ccstr_of_Sesp (a);
    if (name)
    {
      if (idx_name == name) {
        chunks.push("");
        return good;
      }
      Sesp* sp = let_map.lookup(name);
      if (sp) {
        return expression_chunks (chunks, *sp, idx_name);
      }
      chunks.top() += name;
      return good;
    }

    uint u = 0;
    if (uint_of_Sesp (a, &u))
    {
      chunks.top() += u;
      return good;
    }


    key = ccstr_of_Sesp (car_of_Sesp (a));
  }

  if (LegitCk(key, good, "ccstr_of_Sesp()"))
  {}

  if (!good) {
  }
  else if (eq_cstr (key, "(bool)") ||
           eq_cstr (key, "(int)")) {
    chunks.top() += "(";
    expression_chunks (chunks, cadr_of_Sesp (a), idx_name);
    chunks.top() += ")";
  }
  else if (eq_cstr (key, "!")) {
    chunks.top() += "!";
    expression_chunks (chunks, cadr_of_Sesp (a), idx_name);
  }
  else if (eq_cstr (key, "negate")) {
    chunks.top() += "-";
    expression_chunks (chunks, cadr_of_Sesp (a), idx_name);
  }
  else if (eq_cstr (key, "&&") ||
           eq_cstr (key, "||") ||
           eq_cstr (key, "=>") ||
           eq_cstr (key, "==") ||
           eq_cstr (key, "!=") ||
           eq_cstr (key, "+") ||
           eq_cstr (key, "-") ||
           eq_cstr (key, "*") ||
           eq_cstr (key, "/") ||
           eq_cstr (key, "%")) {
    bool pad =
      (eq_cstr (key, "&&") ||
       eq_cstr (key, "||") ||
       eq_cstr (key, "=>"));
    expression_chunks (chunks, cadr_of_Sesp (a), idx_name);
    if (pad)  chunks.top() += " ";
    chunks.top() += key;
    if (pad)  chunks.top() += " ";
    expression_chunks (chunks, caddr_of_Sesp (a), idx_name);
  }
  else if (eq_cstr (key, "xnor")) {
    expression_chunks (chunks, cadr_of_Sesp (a), idx_name);
    chunks.top() += "==";
    expression_chunks (chunks, caddr_of_Sesp (a), idx_name);
  }
  else if (eq_cstr (key, "xor")) {
    expression_chunks (chunks, cadr_of_Sesp (a), idx_name);
    chunks.top() += "!=";
    expression_chunks (chunks, caddr_of_Sesp (a), idx_name);
  }
  else if (eq_cstr (key, "NatDom")) {
    chunks.top() += "Nat % ";
    expression_chunks (chunks, cadr_of_Sesp (a), idx_name);
  }
  else if (eq_cstr (key, "aref")) {
    chunks.top() += ccstr_of_Sesp (cadr_of_Sesp (a));
    chunks.top() += "[";
    expression_chunks (chunks, caddr_of_Sesp (a), idx_name);
    chunks.top() += "]";
  }
  else if (eq_cstr (key, "forall") ||
           eq_cstr (key, "exists") ||
           eq_cstr (key, "unique")
          )
  {
    chunks.top() += key;
    chunks.top() += " ";
    chunks.top() += ccstr_of_Sesp (cadr_of_Sesp (a));
    chunks.top() += " <- ";
    expression_chunks (chunks, caddr_of_Sesp (a), idx_name);
    chunks.top() += " : ";
    expression_chunks (chunks, cadddr_of_Sesp (a), idx_name);
  }
  else {
    good = false;
    DBog1( "No matching string, key is: \"%s\"", key );;
  }

  if (LegitCk( good, allgood, "" )) {}
  return good;
}


  bool
ProtoconFile::eval(Cx::PFmla& pf, Sesp a)
{
  bool good = true;
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
  else if (eq_cstr (key, "==")) {
    if (LegitCk( eval(ipf_b, b), good, "" )) {
      if (LegitCk( eval(ipf_c, c), good, "" )) {
        pf = (ipf_b == ipf_c);
      }
    }
  }
  else if (eq_cstr (key, "!=")) {
    if (LegitCk( eval(ipf_b, b), good, "" )) {
      if (LegitCk( eval(ipf_c, c), good, "" )) {
        pf = (ipf_b != ipf_c);
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
    DBog1( "No matching string, key is: \"%s\"", key );;
  }

  if (LegitCk( good, allgood, "" )) {}
  return good;
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

  Sesp b = cdr_of_Sesp (a);;
  Sesp c = cdr_of_Sesp (b);;

  a = car_of_Sesp (a);
  b = car_of_Sesp (b);
  c = car_of_Sesp (c);

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
  else if (eq_cstr (key, "NatDom")) {
    uint domsz = 0;
    if (LegitCk(eval_gtz (&domsz, b), good, "")) {
      ipf = Cx::IntPFmla( 1, 0, domsz );
    }
  }
  else if (eq_cstr (key, "aref")) {
    const char* name = 0;

    if (LegitCk( b, good, "" ))
      name = ccstr_of_Sesp (b);

    const Xn::VblSymm* symm = 0;
    if (LegitCk( name, good, "" ))
    {
      const Xn::VblSymm** tmp = vbl_map.lookup(name);
      if (LegitCk( tmp, good, "" ))
        symm = *tmp;
    }

    int idx_int = 0;
    if (LegitCk( eval_int (&idx_int, c), good, "" ))
    {
      uint idx = umod_int (idx_int, symm->membs.sz());
      ipf = Cx::IntPFmla(sys->topology.pfmla_vbl(*symm->membs[idx]));
    }
  }
  else {
    good = false;
    DBog1( "No matching string, key is: \"%s\"", key );;
  }

  if (LegitCk( good, allgood, "" )) {}
  return good;
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
  if (LegitCk( legit, allgood, "" )) {}
  return legit;
}

  bool
ProtoconFile::eval_gtz(uint* ret, Sesp sp)
{
  int x = 0;
  bool legit = eval_int (&x, sp);;
  if (LegitCk( x > 0, legit, "" )) {
    *ret = (uint) x;
  }
  if (LegitCk( legit, allgood, "" )) {}
  return legit;
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
  bool legit = true;
  const char* name = 0;

  if (LegitCk( b, legit, "" ))
    name = ccstr_of_Sesp (b);

  const Xn::VblSymm* symm = 0;
  if (LegitCk( name, legit, "" ))
  {
    const Xn::VblSymm** tmp = vbl_map.lookup(name);
    if (LegitCk( tmp, legit, "" ))
      symm = *tmp;
  }

  int idx = 0;
  if (LegitCk( eval_int (&idx, c), legit, "" ))
  {
    *ret = symm->membs[umod_int (idx, symm->membs.sz())];
  }
  if (LegitCk( legit, allgood, "" )) {}
  return legit;
}

  bool
ProtoconFile::lookup_int(int* ret, const Cx::String& name)
{
  const int* val = index_map.lookup(name);
  if (val) {
    *ret = *val;
    return true;
  }

  Sign good = 1;
  Sesp* sp = let_map.lookup(name);
  DoLegit(good, "let_map.lookup()")
    good = !!sp;
  DoLegit(good, "eval_int()")
    good = eval_int(ret, *sp);
  DoLegit(allgood, "")
    allgood = good;
  return good;
}


