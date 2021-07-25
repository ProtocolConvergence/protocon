
#include "conflictfamily.hh"

#include "cx/xfile.hh"

#define FOR_EACH(it,conflict_sets) \
  for (Set<  FlatSet<uint> >::const_iterator it = conflict_sets.begin(); \
       it != conflict_sets.end(); \
       ++it)

#include "namespace.hh"

  ConflictFamily
ConflictFamily::operator-(const ConflictFamily& fam) const
{
  ConflictFamily diff;
  diff.conflict_sets = this->conflict_sets - fam.conflict_sets;
  diff.impossible_set = this->impossible_set - fam.impossible_set;
  return diff;
}

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

  bool
ConflictFamily::exact_conflict_ck(const FlatSet<uint>& test_set) const
{
  FOR_EACH( it, conflict_sets )
  {
    const FlatSet<uint>& conflict_set = *it;
    if (conflict_set == test_set) {
      return true;
    }
  }
  return false;
}

  void
ConflictFamily::add_conflict(const FlatSet<uint>& b)
{
  //Set< FlatSet<uint> > dels;
  for (Set< FlatSet<uint> >::const_iterator it = conflict_sets.begin(); it != conflict_sets.end();)
    //FOR_EACH( it, conflict_sets )
  {
    const FlatSet<uint>& a = *it;
    if (a.subseteq_ck(b)) {
      return;
    }
    if (b.subseteq_ck(a)) {
      //dels << *it;
      Set< FlatSet<uint> >::iterator tmp = it;
      ++it;
      conflict_sets.erase(tmp);
    }
    else {
      ++it;
    }
  }
  //conflict_sets -= dels;
  this->conflict_sets << b;
  if (b.sz() == 1) {
    this->impossible_set << b[0];
  }
  if (this->record_new_conflict_sets) {
    this->new_conflict_sets.push(b);
  }
}

  void
ConflictFamily::add_conflict(const Table<uint>& b)
{
  FlatSet<uint> tmp( b );
  this->add_conflict(tmp);
}

  void
ConflictFamily::add_conflict(const Set<uint>& b)
{
  FlatSet<uint> tmp( b );
  this->add_conflict(tmp);
}

  void
ConflictFamily::add_impossible(uint e)
{
  add_conflict(FlatSet<uint>(&e, 1));
}

  void
ConflictFamily::add_conflicts(const ConflictFamily& fam)
{
  Set< FlatSet<uint> > diff_set =
    fam.conflict_sets - conflict_sets;

  FOR_EACH( it, diff_set )
    this->add_conflict(*it);
}

  void
ConflictFamily::add_conflicts(const Table<uint>& flat_conflicts)
{
  uint i = 0;
  while (i < flat_conflicts.sz()) {
    uint n = flat_conflicts[i++];
    this->add_conflict(FlatSet<uint>(&flat_conflicts[i], n));
    i += n;
  }
}

  void
ConflictFamily::trim(uint max_sz)
{
  if (max_sz == 0)  return;
  Set< FlatSet<uint> > dels;
  FOR_EACH( it, conflict_sets )
  {
    uint sz = (*it).sz();
    if (sz > max_sz) {
      dels << *it;
    }
  }
  conflict_sets -= dels;
}

  void
ConflictFamily::conflict_sizes(Table<uint>& a) const {
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
ConflictFamily::superset_membs(FlatSet<uint>& ret_membs,
                               const FlatSet<uint>& test_set,
                               const FlatSet<uint>& count_set) const
{
  Set<uint> membs;
  FOR_EACH( it, conflict_sets )
  {
    const FlatSet<uint>& conflict_set = *it;
    if (!test_set.subseteq_ck(conflict_set))
      continue;
    uint i = 0;
    uint j = 0;
    while (j < conflict_set.sz()) {
      const uint elem = conflict_set[j];
      if (i >= test_set.sz() || test_set[i] != elem) {
        j += 1;
        if (count_set.elem_ck(elem))
          membs << elem;
      }
      else {
        i += 1;
        j += 1;
      }
    }
  }
  ret_membs = FlatSet<uint>(membs);
}

  bool
ConflictFamily::conflict_membs(Set<uint>* ret_membs,
                               const FlatSet<uint>& test_set,
                               const FlatSet<uint>& count_set) const
{
  Table<uint> diff;
  FOR_EACH( it, conflict_sets )
  {
    if ((*it).subseteq_fuzz_ck(&diff, test_set, 1)) {
      if (diff.sz() == 0)
        return false;
      if (count_set.elem_ck(diff[0]))
        *ret_membs << diff[0];
    }
  }
  return true;
}

  void
ConflictFamily::all_conflicts(Table< FlatSet<uint> >& ret) const
{
  ret.clear();
  FOR_EACH( it, conflict_sets )
  {
    ret.push(*it);
  }
}

  void
ConflictFamily::all_conflicts(Table<uint>& ret) const
{
  ret.clear();
  FOR_EACH( it, conflict_sets )
  {
    const FlatSet<uint>& conflict = *it;
    ret.push(conflict.sz());
    for (uint j = 0; j < conflict.sz(); ++j) {
      ret.push(conflict[j]);
    }
  }
}

  void
ConflictFamily::flush_new_conflicts(Table< FlatSet<uint> >& ret)
{
  if (!this->record_new_conflict_sets) {
    this->all_conflicts(ret);
    this->record_new_conflict_sets = true;
  }
  else {
    ret.flush();
    for (uint i = 0; i < this->new_conflict_sets.sz(); ++i) {
      const FlatSet<uint>& conflict = this->new_conflict_sets[this->new_conflict_sets.sz()-i-1];
      ret.push(conflict);
    }
    this->new_conflict_sets.clear();
  }
}

  void
ConflictFamily::flush_new_conflicts(Table<uint>& ret)
{
  if (!this->record_new_conflict_sets) {
    this->all_conflicts(ret);
    this->record_new_conflict_sets = true;
  }
  else {
    ret.clear();
    for (uint i = 0; i < this->new_conflict_sets.sz(); ++i) {
      const FlatSet<uint>& conflict = this->new_conflict_sets[this->new_conflict_sets.sz()-i-1];
      ret.push(conflict.sz());
      for (uint j = 0; j < conflict.sz(); ++j) {
        ret.push(conflict[j]);
      }
    }
    this->new_conflict_sets.clear();
  }
}

  void
ConflictFamily::flush_new_conflicts()
{
  this->new_conflict_sets.clear();
  this->record_new_conflict_sets = true;
}

  void
ConflictFamily::clear()
{
  conflict_sets.clear();
  impossible_set.clear();
  new_conflict_sets.clear();
  record_new_conflict_sets = false;
}

  bool
ConflictFamily::sat_ck() const
{
  if (conflict_sets.sz() != 1) {
    return true;
  }
  const FlatSet<uint>& e = conflict_sets.elem();
  return (e.sz() > 0);
}

  void
ConflictFamily::oput_conflict_sizes(std::ostream& of) const
{
  Table<uint> t;
  this->conflict_sizes(t);
  for (uint i = 0; i < t.sz(); ++i) {
    of << ' ' << i << ':' << t[i];
  }
  of << '\n';
}

  void
ConflictFamily::oput(std::ostream& of) const
{
  of << conflict_sets.sz() << '\n';
  FOR_EACH( it, conflict_sets )
  {
    of << (*it).sz() << ' ';
    const FlatSet<uint>& conflict_set = *it;
    for (uint i = 0; i < conflict_set.sz(); ++i)
      of << ' ' << conflict_set[i];
    of << '\n';
  }
}

  void
ConflictFamily::xget(XFile& xf)
{
  conflict_sets.clear();
  impossible_set.clear();

  zuint n = 0;
  xf >> n;

  Table<uint> conflict_set;
  for (zuint i = 0; i < n; ++i)
  {
    uint sz = 0;
    xf >> sz;
    conflict_set.resize(sz);
    for (uint j = 0; j < sz; ++j)
    {
      xf >> conflict_set[j];
      if (!xf.good())  return;
    }
    if (conflict_set.sz() == 1)
      impossible_set << conflict_set[0];
    conflict_sets << FlatSet<uint>(conflict_set);
  }
}

END_NAMESPACE

