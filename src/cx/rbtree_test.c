/**
 * \file rbtree_test.c
 * Tests for red-black tree.
 **/

#include "syscx.h"

#include "associa.h"
#include "fileb.h"
#include "lgtable.h"
#include "ofile.h"
#include "rbtree.h"


typedef struct TNode TNode;
struct TNode
{
  RBTNode rbt;
  const char* key;
  uint val;
};

  void
lose_TNode (BSTNode* x)
{
  TNode* a = CastUp( TNode, rbt, CastUp( RBTNode, bst, x ) );
  a->key = 0;
}

static
  uint
countup_black_RBTNode (const RBTNode* x)
{
  uint n = 0;
  Claim( x->bst.joint );
  do {
    n += (x->red ? 0 : 1);
    x = CastUp( RBTNode, bst, x->bst.joint );
  } while (x->bst.joint);
  return n;
}

static
  void
claim_TNode (BSTNode* x, void* args)
{
  RBTNode* b = CastUp( RBTNode, bst, x );
  uint* n = (uint*)((void**)args)[0];
  uint* nblack = (uint*)((void**)args)[1];
  *n += 1;

  Claim( x->joint );

  Claim( x->joint );
  Claim2( x ,==, x->joint->split[side_of_BSTNode (x)]);

  if (x->split[0])
    Claim2( x ,==, x->split[0]->joint );
  if (x->split[1])
    Claim2( x ,==, x->split[1]->joint );

  if (b->red) {
    b = CastUp( RBTNode, bst, x->joint );
    Claim( !b->red );
  }
  if (!x->split[0] || !x->split[1]) {
    uint c = countup_black_RBTNode (b);
    if (*nblack == UINT_MAX)
      *nblack = c;
    else
      Claim2( *nblack ,==, c );
  }
}

static
  void
claim_BSTree (BSTree* t, uint n_expect)
{
  uint n_result;
  uint nblack = UINT_MAX;
  void* args[2];
  args[0] = &n_result;
  args[1] = &nblack;

  n_result = 0;
  walk_BSTree (t, Yes, claim_TNode, args);
  Claim2( n_expect ,==, n_result );
  n_result = 0;
  walk_BSTree (t, Nil, claim_TNode, args);
  Claim2( n_expect ,==, n_result );
  n_result = 0;
  walk_BSTree (t, May, claim_TNode, args);
  Claim2( n_expect ,==, n_result );
}

static
  void
insert_TNode (RBTree* t, LgTable* lgt,
    const char* key, uint val, uint* n_expect)
{
  TNode* a = (TNode*) take_LgTable (lgt);
  a->key = key;
  a->val = val;
  insert_RBTree (t, &a->rbt);
  *n_expect += 1;
  claim_BSTree (&t->bst, *n_expect);
}

  void
output_dot_fn (BSTNode* x, void* args)
{
  TNode* a = CastUp( TNode, rbt, CastUp( RBTNode, bst, x ) );
  OFile* of = (OFile*) ((void**)args)[0];

  printf_OFile (of, "q%u [label = \"%s\", color = \"%s\"];\n",
      a->val,
      a->key,
      (a->rbt.red) ? "red" : "black");

  if (x->joint) {
    TNode* b = CastUp( TNode, rbt, CastUp( RBTNode, bst, x->joint ) );
    printf_OFile (of, "q%u -> q%u;\n", b->val, a->val);
  }
  flush_OFile (of);
}

  void
output_dot (BSTree* t)
{
  void* args[1];
  OFileB ofb[] = {DEFAULT_OFileB};
  OFile* of = &ofb->of;
  args[0] = of;

  open_FileB (&ofb->fb, "", "out.dot");

  oput_cstr_OFile (of, "digraph tree {\n");
  output_dot_fn (t->sentinel, args);
  walk_BSTree (t, Yes, output_dot_fn, args);
  oput_cstr_OFile (of, "}\n");
  lose_OFileB (ofb);
}

static
  TNode*
find_TNode (RBTree* t, const char* s)
{
  BSTNode* x = find_BSTree (&t->bst, &s);
  if (!x)  return 0;
  return CastUp( TNode, rbt, CastUp( RBTNode, bst, x ) );
}

static
  void
remove_TNode (RBTree* t, LgTable* lgt,
    const char* key, uint* n_expect)
{
  TNode* a = find_TNode (t, key);
  Claim( a );
  remove_RBTree (t, &a->rbt);
  lose_TNode (&a->rbt.bst);
  give_LgTable (lgt, a);
  *n_expect -= 1;
  claim_BSTree (&t->bst, *n_expect);
}

/** \test
 * Rigorously test red-black tree with different combinations of insert
 * and remove operations.
 * Set up and tear down a tree of 26 strings (ascii letters) in many different
 * orders. To ensure many orders, use sequential multiples of coprimes with 26
 * to index the array of keys.
 *
 * Ex: The following sequence is generated from the first 26 multiples of 3.\n
 * 0 3 6 9 12 15 18 21 24 1 4 7 10 13 16 19 22 25 2 5 8 11 14 17 20 23
 **/
  void
testfn_RBTree ()
{
  static const char* const keys[] = {
    "a", "b", "c", "d", "e", "f", "g",
    "h", "i", "j", "k", "l", "m", "n",
    "o", "p", "q", "r", "s", "t", "u",
    "v", "w", "x", "y", "z"
  };
  static const uint muls[] = {
    1, 3, 5, 7, 9, 11, 15, 17, 19, 21
  };
  const uint nkeys = ArraySz( keys );
  const uint nmuls = ArraySz( muls );
  TNode sentinel;
  PosetCmp cmp =
    dflt3_PosetCmp (offsetof( TNode, rbt ),
        offsetof( TNode, key ),
        (PosetCmpFn) cmp_cstr_loc);
  DecloStack1( RBTree, t, dflt2_RBTree (&sentinel.rbt, cmp) );
  DecloStack1( LgTable, lgt, dflt1_LgTable (sizeof(TNode)) );
  uint n_expect = 0;
  uint mi, mj, i;

  sentinel.key = "sentinel";
  sentinel.val = nkeys;

  UFor( mi, nmuls ) {
    UFor( mj, nmuls ) {
      UFor( i, nkeys ) {
        const uint idx = (muls[mi] * i) % nkeys;
        insert_TNode (t, lgt, keys[idx], idx, &n_expect);
      }
#if 0
      output_dot (&t->bst);
#endif
      UFor( i, nkeys ) {
        const uint idx = (muls[mj] * i) % nkeys;
        remove_TNode (t, lgt, keys[idx], &n_expect);
      }
    }
  }

  lose_BSTree (&t->bst, lose_TNode);
  lose_LgTable (lgt);
}

/** \test
 * Test Associa structure.
 * \sa testfn_RBTree()
 **/
static
  void
testfn_Associa ()
{
  static const char* const keys[] = {
    "a", "b", "c", "d", "e", "f", "g",
    "h", "i", "j", "k", "l", "m", "n",
    "o", "p", "q", "r", "s", "t", "u",
    "v", "w", "x", "y", "z"
  };
  static const uint muls[] = {
    1, 3, 5, 7, 9, 11, 15, 17, 19, 21
  };
  const uint nkeys = ArraySz( keys );
  const uint nmuls = ArraySz( muls );
  Associa map[1];
  uint n_expect = 1; /* Sentinel node.*/
  uint mi, mj, i;

  InitAssocia( AlphaTab, uint, *map, cmp_AlphaTab );

  Claim2( map->nodes.sz ,==, n_expect );
  UFor( mi, nmuls ) {
    UFor( mj, nmuls ) {
      UFor( i, nkeys ) {
        const uint idx = (muls[mi] * i) % nkeys;
        const AlphaTab key = dflt1_AlphaTab (keys[idx]);
        if (mj % 2 == 0) {
          insert_Associa (map, &key, &idx);
        }
        else {
          bool added = false;
          Assoc* assoc = ensure1_Associa (map, &key, &added);
          Claim( added );
          val_fo_Assoc (map, assoc, &idx);
        }
        ++ n_expect;
        Claim2( map->nodes.sz ,==, n_expect );
      }


      UFor( i, nkeys ) {
        const uint idx = (muls[mj] * i) % nkeys;
        const AlphaTab key = dflt1_AlphaTab (keys[idx]);
        Assoc* a;
        if (mj % 2 == 0) {
          a = lookup_Associa (map, &key);
        }
        else {
          bool added = true;
          a = ensure1_Associa (map, &key, &added);
          Claim( !added );
        }
        Claim( a );
        {
          uint val = *(uint*) val_of_Assoc (map, a);
          Claim2( idx ,==, val );
        }
        give_Associa (map, a);
        -- n_expect;
        Claim2( map->nodes.sz ,==, n_expect );
      }
    }
  }

  /* Claim the sentinel still exists.*/
  Claim2( map->nodes.sz ,==, 1 );
  Claim2( n_expect ,==, 1 );
  lose_Associa (map);
}

int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);
  (void) argi;

  testfn_RBTree();
  testfn_Associa();

  lose_sysCx ();
  return 0;
}
