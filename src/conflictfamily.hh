
#ifndef ConflictFamily_HH_
#define ConflictFamily_HH_

#include "cx/synhax.hh"
#include "cx/set.hh"

#include "namespace.hh"

class ConflictFamily
{
private:
  Set< FlatSet<uint> > conflict_sets;
  Table< FlatSet<uint> > new_conflict_sets;
  bool record_new_conflict_sets;

public:
  Set<uint> impossible_set;

  ConflictFamily operator-(const ConflictFamily& fam) const;

  ConflictFamily()
    : record_new_conflict_sets(false)
  {}

  bool conflict_ck(const FlatSet<uint>& test_set) const;
  bool exact_conflict_ck(const FlatSet<uint>& test_set) const;
  void add_conflict(const FlatSet<uint>& b);
  void add_conflict(const Table<uint>& b);
  void add_conflict(const Set<uint>& b);
  void add_impossible(uint e);
  void add_conflicts(const ConflictFamily& fam);
  void add_conflicts(const Table<uint>& flat_conflicts);
  void trim(uint max_sz);
  void conflict_sizes(Table<uint>& a) const;
  void superset_membs(FlatSet<uint>& ret_membs,
                      const FlatSet<uint>& test_set,
                      const FlatSet<uint>& count_set) const;
  bool conflict_membs(Set<uint>* ret_membs,
                      const FlatSet<uint>& test_set,
                      const FlatSet<uint>& count_set) const;
  void all_conflicts(Table< FlatSet<uint> >& ret) const;
  void all_conflicts(Table<uint>& ret) const;
  void flush_new_conflicts(Table< FlatSet<uint> >& ret);
  void flush_new_conflicts(Table<uint>& ret);
  void flush_new_conflicts();
  void clear();
  bool sat_ck() const;

  void oput_conflict_sizes(OFile& of) const;
  void oput(OFile& of) const;
  void xget(XFile& xf);
};

inline OFile&
operator<<(OFile& of, const ConflictFamily& conflicts)
{ conflicts.oput(of); return of; }

inline XFile&
operator>>(XFile& xf, ConflictFamily& conflicts)
{ conflicts.xget(xf); return xf; }

END_NAMESPACE
#endif

