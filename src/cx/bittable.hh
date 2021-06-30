/**
 * \file bittable.hh
 * C++ bit array.
 **/
#ifndef BitTable_HH_
#define BitTable_HH_

#include "synhax.hh"
extern "C" {
#include "bittable.h"
}

namespace Cx {
namespace C {
  using ::BitTable;
}

class BitTable
{
private:
  C::BitTable bt;
public:

  class BitTableElement {
    C::BitTable bt;
    zuint idx;
  public:
    BitTableElement(C::BitTable _bt, zuint _idx)
      : bt(_bt)
      , idx(_idx)
    {}

    BitTableElement& operator=(Bit b)
    {
      setb_BitTable (bt, idx, b);
      return *this;
    }

    operator bool() const
    { return ck_BitTable (bt, idx); }
  };

  BitTable() {
    bt = dflt_BitTable ();
  }
  BitTable(zuint n, Bit b) {
    bt = cons2_BitTable (n, b);
  }
  BitTable(const BitTable& a) {
    bt = cons1_BitTable (a.sz());
    op_BitTable (bt, BitOp_IDEN1, a.bt);
  }
  BitTable(const C::BitTable& a) {
    bt = cons1_BitTable (a.sz);
    op_BitTable (bt, BitOp_IDEN1, a);
  }
  explicit BitTable(const std::vector<bool>& a) {
    bt = dflt_BitTable ();
    (*this) = a;
  }
  BitTable& operator=(const BitTable& a) {
    size_fo_BitTable (&bt, a.sz());
    op_BitTable (bt, BitOp_IDEN1, a.bt);
    return *this;
  }
  BitTable& operator=(const std::vector<bool>& a) {
    size_fo_BitTable (&bt, a.size());
    for (zuint i = 0; i < bt.sz; ++i) {
      setb_BitTable (bt, i, a[i] ? 1 : 0);
    }
    return *this;
  }
  ~BitTable() {
    lose_BitTable (&bt);
  }

  BitTable& operator&=(const C::BitTable& a) {
    op_BitTable (bt, BitOp_AND, a);
    return *this;
  }
  BitTable& operator|=(const C::BitTable& a) {
    op_BitTable (bt, BitOp_OR, a);
    return *this;
  }
  BitTable& operator-=(const C::BitTable& a) {
    op_BitTable (bt, BitOp_NIMP, a);
    return *this;
  }
  BitTable& operator&=(const BitTable& a) { return *this &= a.bt; }
  BitTable& operator|=(const BitTable& a) { return *this |= a.bt; }
  BitTable& operator-=(const BitTable& a) { return *this -= a.bt; }

  zuint sz() const {
    return bt.sz;
  }
  zuint size() const { return this->sz(); }

  void wipe(Bit b) {
    wipe_BitTable (bt, b);
  }

  void grow(zuint capac) {
    grow_BitTable (&bt, capac);
  }

  void resize(zuint capac) {
    size_fo_BitTable (&bt, capac);
  }
  void clear() {
    this->resize(0);
  }

  Bit operator[](zuint i) const {
    return ck_BitTable (bt, i);
  }

  BitTableElement operator[](zuint i) {
    return BitTableElement(bt, i);
  }

  bool operator==(const BitTable& b) const {
    return (this->cmp(b) == 0);
  }
  bool operator!=(const BitTable& b) const {
    return !(*this == b);
  }

  Sign cmp(const BitTable& b) const
  {
    return cmp_BitTable (bt, b.bt);
  }

  bool operator<=(const BitTable& b) const {
    return (this->cmp(b) <= 0);
  }
  bool operator<(const BitTable& b) const {
    return (this->cmp(b) < 0);
  }
  bool operator>(const BitTable& b) const {
    return (this->cmp(b) > 0);
  }
  bool operator>=(const BitTable& b) const {
    return (this->cmp(b) >= 0);
  }

  Bit set0(zuint idx) { return set0_BitTable (bt, idx); }
  Bit set1(zuint idx) { return set1_BitTable (bt, idx); }
  bool ck(zuint idx) const { return ck_BitTable (bt, idx); }

  void set(zuint idx, uint nbits, uint z)
  { set_uint_BitTable (bt, idx, nbits, z); }
  uint get(zuint idx, uint nbits) const
  { return get_uint_BitTable (bt, idx, nbits); }

  bool subseteq_ck(const BitTable& b) const {
    return fold_map2_BitTable (BitOp_AND, BitOp_IMP, this->bt, b.bt);
  }

  bool sat_ck() const {
    return sat_ck_BitTable (bt);
  }

  zuint begidx() const {
    return begidx_BitTable (bt);
  }
  zuint nextidx(zuint i) const {
    return nextidx_BitTable (bt, i);
  }
  void nextidx(zuint* i) const {
    *i = nextidx_BitTable (bt, *i);
  }

  zuint count() const {
    return count_BitTable (bt);
  }
};

inline
  zuint
sz_of (const BitTable& t)
{
  return t.sz();
}
}

#endif

