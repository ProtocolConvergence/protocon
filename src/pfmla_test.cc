
extern "C" {
#include "cx/syscx.h"
}

#include "cx/synhax.hh"
#include "pfmla.hh"

#include "namespace.hh"

static
  void
TestPFmla()
{
  PFmlaCtx ctx;

  const PFmlaVbl& w = ctx.vbl( ctx.add_vbl("w", 4) );
  const PFmlaVbl& x = ctx.vbl( ctx.add_vbl("x", 4) );
  const PFmlaVbl& y = ctx.vbl( ctx.add_vbl("y", 7) );

  uint w_list_id = ctx.add_vbl_list();
  uint x_list_id = ctx.add_vbl_list();
  ctx.add_to_vbl_list(w_list_id, id_of(w));
  ctx.add_to_vbl_list(x_list_id, id_of(x));

  P::Fmla pf( x == y );

  Claim( P::Fmla(true).tautology_ck() );
  Claim( (x == x).tautology_ck() );
  Claim( (x == y).equiv_ck((x == 0 && y == 0) ||
                           (x == 1 && y == 1) ||
                           (x == 2 && y == 2) ||
                           (x == 3 && y == 3)) );

  Claim( (x == y).equiv_ck(y == x) );
  Claim( x.equiv_ck(ctx.vbl("x")) );

  // Add another variable, ensure it doesn't screw up the existing PFmla.
  const PFmlaVbl& z = ctx.vbl( ctx.add_vbl("z", 5) );
  Claim( pf.equiv_ck(x == y) );
  Claim( pf.overlap_ck(x == z) );

  // Ensure substitution smooths the source variables.
  P::Fmla pf_a = (w == 2);
  P::Fmla pf_b = (x == 2);

  Claim( !pf_a.equiv_ck(pf_b) );
  pf = pf_b.substitute_new_old(w_list_id, x_list_id);
  Claim( pf.equiv_ck(pf_a) );
  pf = pf_a.substitute_new_old(x_list_id, w_list_id);
  Claim( pf.equiv_ck(pf_b) );

  // Test picking.
  pf = (x == y).pick_pre();
  Claim2( pf ,<=, (x == y) );
  Claim( !pf.equiv_ck(x == y) );
}

static
  void
TestIntPFmla()
{
  PFmlaCtx ctx;
  const uint n = 5;
  const PFmlaVbl& x = ctx.vbl( ctx.add_vbl("x", n) );
  const PFmlaVbl& y = ctx.vbl( ctx.add_vbl("y", n) );
  const PFmlaVbl& z = ctx.vbl( ctx.add_vbl("z", n) );

  // Invariant for (game of cards) agreement protocol.
  P::Fmla pf( false );
  for (uint a = 0; a < n; ++a) {
    for (uint b = 0; b < n; ++b) {
      // Yeah, this last loop definitely isn't needed.
      // But there's no harm.
      for (uint c = 0; c < n; ++c) {
        if (decmod(a, b, n) == decmod(b, c, n)) {
          pf |= (x == a && y == b && z == c);
        }
      }
    }
  }
  Claim( pf.equiv_ck(((y - x) % n) == ((z - y) % n)) );

  // Invariant for sum-not-(n-1) protocol.
  {
    const uint target = n-1;
    const uint domsz = n;
    pf = true;
    // (x[r-1] + x[r]) % domsz != target
    // Equivalently:
    // For all i,
    for (uint i = 0; i < domsz; ++i) {
      // (x[r-1] == i) implies (x[r] != ((target - i) % domsz))
      pf &= ((x != i) | (y != decmod(target, i, domsz)));
    }
    Claim( pf.equiv_ck(x + y != (int) target) );
  }

  // Ensure the action (x < y --> x:=y; y:=x;)
  // can be specified using img_eq(IntPFmla).
  pf = (x < y);
  IntPFmla ipf;
  ipf = y;  pf &= x.img_eq(ipf);
  ipf = x;  pf &= y.img_eq(ipf);
  for (uint a = 0; a < n; ++a) {
    for (uint b = 0; b < n; ++b) {
      if (a < b) {
        Claim( ((x == b) & (y == a)).equiv_ck(pf.img((x == a) & (y == b))) );
      }
      else {
        Claim( !pf.img((x == a) & (y == b)).sat_ck() );
      }
    }
  }
}

END_NAMESPACE

int main(int argc, char** argv)
{
  using namespace PROTOCON_NAMESPACE;
  int argi = init_sysCx (&argc, &argv);
  (void) argi;

  TestPFmla();
  TestIntPFmla();

  lose_sysCx ();
  return 0;
}

