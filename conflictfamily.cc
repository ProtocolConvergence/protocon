
#include "conflictfamily.hh"

#include "cx/ofile.hh"
#include "cx/xfile.hh"

#define FOR_EACH(it,conflict_sets) \
  for (Cx::Set< Cx:: FlatSet<uint> >::const_iterator it = conflict_sets.begin(); \
       it != conflict_sets.end(); \
       ++it)

  bool
ConflictFamily::conflict_ck(const FlatSet<uint>& test_set) const
{
  //if (conflict_sets.elem_ck(test_set))
  //  return true;

  FOR_EACH( it, conflict_sets )
  {
    const FlatSet<uint>& conflict_set = *it;
    if (conflict_set.subseteq_ck(test_set)) {
      return true;
    }
  }
  return false;
}

  void
ConflictFamily::add_conflict(const FlatSet<uint>& b)
{
  //Set< Cx::FlatSet<uint> > dels;
  for (Cx::Set< Cx:: FlatSet<uint> >::const_iterator it = conflict_sets.begin(); it != conflict_sets.end();)
    //FOR_EACH( it, conflict_sets )
  {
    const FlatSet<uint>& a = *it;
    if (a.subseteq_ck(b)) {
      return;
    }
    if (b.subseteq_ck(a)) {
      //dels |= *it;
      Cx::Set< Cx::FlatSet<uint> >::iterator tmp = it;
      ++it;
      conflict_sets.erase(tmp);
    }
    else {
      ++it;
    }
  }
  if (b.sz() == 1) {
    this->impossible_set |= b[0];
  }
  //conflict_sets -= dels;
  conflict_sets |= b;
}

  void
ConflictFamily::add_conflict(const Cx::Table<uint>& b)
{
  Cx::FlatSet<uint> tmp( b );
  this->add_conflict(tmp);
}

  void
ConflictFamily::add_conflict(const Cx::Set<uint>& b)
{
  Cx::FlatSet<uint> tmp( b );
  this->add_conflict(tmp);
}

  void
ConflictFamily::add_conflicts(const ConflictFamily& fam)
{
  Cx::Set< Cx::FlatSet<uint> > diff_set =
    fam.conflict_sets - conflict_sets;

  FOR_EACH( it, diff_set )
    this->add_conflict(*it);
}

  void
ConflictFamily::conflict_sizes(Cx::Table<uint>& a) const {
  a.clear();
  FOR_EACH( it, conflict_sets )
  {
    uint sz = (*it).sz();
    if (sz >= a.sz()) {
      a.grow(1 + sz - a.sz(), 0);
    }
    a[sz] += 1;
  }
}

  void
ConflictFamily::oput_conflict_sizes(Cx::OFile& of) const
{
  Cx::Table<uint> t;
  this->conflict_sizes(t);
  for (uint i = 0; i < t.sz(); ++i) {
    of << ' ' << i << ':' << t[i];
  }
  of << '\n';
}

  void
ConflictFamily::oput(Cx::OFile& of) const
{
  of << conflict_sets.sz() << '\n';
  FOR_EACH( it, conflict_sets )
  {
    of << ' ' << (*it).sz();
  }

  of << '\n';

  FOR_EACH( it, conflict_sets )
  {
    const Cx::FlatSet<uint>& conflict_set = *it;
    for (uint i = 0; i < conflict_set.sz(); ++i)
      of << ' ' << conflict_set[i];
    of << '\n';
  }
}

  void
ConflictFamily::xget(Cx::XFile& xf)
{
  conflict_sets.clear();
  impossible_set.clear();

  Cx::Table<uint> sizes;
  ujint n = 0;
  xf >> n;
  if (!xf.good())  return;
  for (ujint i = 0; i < n; ++i)
  {
    ujint sz = 0;
    xf >> sz;
    if (!xf.good())  return;
    sizes.push(sz);
  }

  for (ujint i = 0; i < n; ++i)
  {
    Cx::Table<uint> conflict_set(sizes[i]);
    for (uint j = 0; j < sizes[i]; ++j)
    {
      xf >> conflict_set[j];
      if (!xf.good())  return;
    }
    if (conflict_set.sz() == 1)
      impossible_set |= conflict_set[0];
    conflict_sets |= Cx::FlatSet<uint>(conflict_set);
  }
}

