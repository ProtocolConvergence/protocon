
#ifndef ConflictFamily_HH_
#define ConflictFamily_HH_

#include "cx/synhax.hh"
#include "cx/set.hh"

namespace Cx {
  class XFile;
  class OFile;
}

class ConflictFamily;

class ConflictFamily
{
private:
  Cx::Set< Cx::FlatSet<uint> > conflict_sets;

public:
  Cx::Set<uint> impossible_set;

  ConflictFamily operator-(const ConflictFamily& fam) const;


  bool conflict_ck(const FlatSet<uint>& test_set) const;
  bool exact_conflict_ck(const FlatSet<uint>& test_set) const;
  void add_conflict(const FlatSet<uint>& b);
  void add_conflict(const Cx::Table<uint>& b);
  void add_conflict(const Cx::Set<uint>& b);
  void add_conflicts(const ConflictFamily& fam);
  void trim(uint max_sz);
  void conflict_sizes(Cx::Table<uint>& a) const;
  void superset_membs(FlatSet<uint>& ret_membs,
                      const FlatSet<uint>& test_set,
                      const FlatSet<uint>& count_set) const;
  bool conflict_membs(Set<uint>* ret_membs,
                      const FlatSet<uint>& test_set,
                      const FlatSet<uint>& count_set) const;
  void all_conflicts(Cx::Table< FlatSet<uint> >& ret) const;
  void clear();
  bool sat_ck() const;

  void oput_conflict_sizes(Cx::OFile& of) const;
  void oput(Cx::OFile& of) const;
  void xget(Cx::XFile& xf);
};

inline Cx::OFile&
operator<<(Cx::OFile& of, const ConflictFamily& conflicts)
{ conflicts.oput(of); return of; }

inline Cx::XFile&
operator>>(Cx::XFile& xf, ConflictFamily& conflicts)
{ conflicts.xget(xf); return xf; }

#endif

