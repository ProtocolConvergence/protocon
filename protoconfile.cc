

#include "protoconfile.hh"

  bool
ProtoconFile::add_variables(Sesp vbl_name_sp, Sesp vbl_nmembs_sp, Sesp vbl_dom_sp)
{
  bool good = true;
  const char* name = 0;
  uint nmembs = 0;
  uint domsz = 0;

  name = ccstr_of_Sesp (vbl_name_sp);
  if (LegitCk(name, good, ""))
  {}
  if (LegitCk(uint_of_Sesp (cadr_of_Sesp (vbl_nmembs_sp), &nmembs), good, ""))
  {}
  if (LegitCk(uint_of_Sesp (cadr_of_Sesp (vbl_dom_sp), &domsz), good, ""))
  {
    // TODO
    // We shouldn't be able to get a domsz so easily.
    // We should evaluate some expression... this allows N-1 to be the domain size..
    Xn::VblSymm* symm = sys->topology.add_variables(name, nmembs, domsz);
    vbl_map[name] = symm;
  }
  return good;
}

  bool
ProtoconFile::add_processes(Sesp pc_name, Sesp idx_name, Sesp npcs)
{
  bool good = true;
  const char* name_a = ccstr_of_Sesp (pc_name);
  const char* name_b = ccstr_of_Sesp (idx_name);
  if (LegitCk(name_a && name_b, good, "")) {
    uint domsz = 0;
    if (LegitCk(uint_of_Sesp (cadr_of_Sesp (npcs), &domsz), good, "")) {
      sys->topology.add_processes(name_a, domsz);
      Claim2( index_map.sz() ,==, 0 );
    }
  }
  return good;
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
      if (LegitCk( eval(ipf, vbl_idx_sp), legit, "" ))
      {}
      if (LegitCk( ipf.state_map.sz() == 1, legit, "" )) {
        indices.membs[i] = ipf.state_map[0];
      }
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
    index_map.erase(idx_name);
  }
  return good;
}

  bool
ProtoconFile::add_legit(Sesp legit_sp)
{
  bool good = true;

  Cx::PFmla pf;
  if (LegitCk( eval(pf, legit_sp), good, "" ))
    sys->invariant &= pf;

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
      if (LegitCk( idx_name == name, good, "" )) {
        chunks.push("");
      }
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
           eq_cstr (key, "==") ||
           eq_cstr (key, "!=") ||
           eq_cstr (key, "+") ||
           eq_cstr (key, "-") ||
           eq_cstr (key, "*") ||
           eq_cstr (key, "/") ||
           eq_cstr (key, "%")) {
    expression_chunks (chunks, cadr_of_Sesp (a), idx_name);
    chunks.top() += key;
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
  else {
    good = false;
    DBog1( "No matching string, key is: \"%s\"", key );;
  }

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
  }
  else {
    good = false;
    DBog1( "No matching string, key is: \"%s\"", key );;
  }

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
      const int* val = index_map.lookup(name);
      if (LegitCk( val, good, "index_map.lookup(name)" )) {
        ipf = Cx::IntPFmla( *val );
        //DBog2("index %s is: %d", name, *val);
      }
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
    if (LegitCk(uint_of_Sesp (b, &domsz), good, "")) {
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

    bool ev = false;
    if (LegitCk( symm, good, "" ))
      ev = eval(ipf, c);

    if (LegitCk( ev, good, "eval()" ))  {}
    if (LegitCk( ipf.state_map.sz() == 1, good, "" ))
    {
      uint idx = umod_int (ipf.state_map[0], symm->membs.sz());
      ipf = Cx::IntPFmla(sys->topology.pfmla_vbl(*symm->membs[idx]));
    }
  }
  else {
    good = false;
    DBog1( "No matching string, key is: \"%s\"", key );;
  }


  return good;
}

