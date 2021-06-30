/**
 * \file bstree.c
 * Binary search tree.
 **/
#ifndef __OPENCL_VERSION__
#include "bstree.h"
#include <assert.h>

#define positive_bit( x )  ((x) > 0 ? 1 : 0)

  BSTree
dflt2_BSTree (BSTNode* sentinel, PosetCmp cmp)
{
  BSTree t;
  sentinel->joint = 0;
  sentinel->split[0] = 0;
  sentinel->split[1] = 0;
  t.sentinel = sentinel;
  t.cmp = cmp;
  return t;
}

  void
init_BSTree (BSTree* t, BSTNode* sentinel, PosetCmp cmp)
{
  *t = dflt2_BSTree (sentinel, cmp);
}

  void
lose_BSTree (BSTree* t, void (* lose) (BSTNode*))
{
  BSTNode* y = root_of_BSTree (t);

  while (y)
  {
    BSTNode* x = y;
    Bit side = 0;

    /* Descend to the lo side.*/
    do
    {
      y = x;
      x = x->split[0];
    } while (x);

    /* Ascend until we can descend to the hi side.*/
    if (!y->split[1])  do
    {
      x = y;
      y = x->joint;
      side = side_of_BSTNode (x);
      lose (x);
    } while (y->joint && (side == 1 || !y->split[1]));

    y = (y->joint ? y->split[1] : 0);
  }
}

/**
 * Preorder, postorder, and inorder traversals are supported by
 * values of Nil, Yes, and May for /postorder/ respectively.
 **/
  void
walk_BSTree (BSTree* t, Trit postorder,
    void (* f) (BSTNode*, void*), void* dat)
{
  BSTNode* y = root_of_BSTree (t);

  while (y)
  {
    BSTNode* x = y;
    Bit side = 0;

    /* Descend to the lo side.*/
    do
    {
      if (postorder == Nil)  f (x, dat);
      y = x;
      x = x->split[0];
    } while (x);

    /* Ascend until we can descend to the hi side.*/
    if (!y->split[1])  do
    {
      if (postorder == May && side == 0)  f (y, dat);
      x = y;
      y = x->joint;
      side = side_of_BSTNode (x);
      if (postorder == Yes)  f (x, dat);
    } while (y->joint && (side == 1 || !y->split[1]));

    if (postorder == May && y->joint)  f (y, dat);
    y = (y->joint ? y->split[1] : 0);
  }
}

  BSTNode*
find_BSTree (BSTree* t, const void* key)
{
  BSTNode* y = root_of_BSTree (t);

  while (y)
  {
    Sign si = poset_cmp_lhs (t->cmp, key, y);
    if (si == 0)  return y;
    y = y->split[positive_bit (si)];
  }
  return 0;
}

  void
insert_BSTree (BSTree* t, BSTNode* x)
{
  BSTNode* a = t->sentinel;
  BSTNode* y = root_of_BSTree (t);
  Bit side = side_of_BSTNode (y);

  while (y)
  {
    side = positive_bit (poset_cmp (t->cmp, x, y));
    a = y;
    y = y->split[side];
  }

  a->split[side] = x;
  x->joint = a;
  x->split[0] = 0;
  x->split[1] = 0;
}

/** If a node matching /x/ exists, return that node.
 * Otherwise, add /x/ to the tree and return it.
 **/
  BSTNode*
ensure_BSTree (BSTree* t, BSTNode* x)
{
  BSTNode* a = t->sentinel;
  BSTNode* y = root_of_BSTree (t);
  Bit side = side_of_BSTNode (y);

  while (y)
  {
    Sign si = poset_cmp (t->cmp, x, y);
    if (si == 0)  return y;
    side = positive_bit (si);
    a = y;
    y = y->split[side];
  }

  a->split[side] = x;
  x->joint = a;
  x->split[0] = 0;
  x->split[1] = 0;
  return x;
}

/**
 * Ensure /x/ exists in the tree.
 * It replaces a matching node if one exists.
 * The matching node (which was replaced) is returned.
 * If no matching node was replaced, 0 is returned.
 **/
  BSTNode*
setf_BSTree (BSTree* t, BSTNode* x)
{
  BSTNode* y = ensure_BSTree (t, x);
  if (y == x)  return 0;
  x->joint = y->joint;
  x->joint->split[side_of_BSTNode (y)] = x;
  join_BSTNode (x, y->split[0], 0);
  join_BSTNode (x, y->split[1], 1);
  return y;
}

/** Remove a given node {y} from the tree.
 *
 * {y} will hold information about what had to be moved,
 * which is used by the red-black tree removal.
 * {y->joint} will hold {b} in the diagrams below.
 * {y->split} will hold the new split of {b} that changed depth.
 **/
  void
remove_BSTNode (BSTNode* y)
{
  Bit side_y = side_of_BSTNode (y);
  Bit side;
#define oside (!side)
  BSTNode* b;
  BSTNode* x;
  uint i;

  /* This is the only case that leaves {y->joint} unchanged.
   * {x} can be Nil.
   **** OLD ********* NEW *** AUX ***
   *     b             b       b
   *    / \           / \      |
   *  0*   y'  -->  0*   *x    y
   *      /                     \
   *    x*                       *x
   */
  for (i = 0; i < 2; ++i) {
    side = (Bit) i;
    if (!y->split[oside])
    {
      x = y->split[side];
      join_BSTNode (y->joint, x, side_y);
      /* b = y->joint; */
      /* y->joint = b; */
      y->split[side_y] = x;
      y->split[!side_y] = 0;
      return;
    }
  }

  /* We know {1} exists.
   ****** OLD ******** NEW ***** AUX ***
   *       y'           b         b
   *      / \          / \        |
   *     b   1  -->  0*   1       y
   *    /                        /
   *  0*                       0*
   */
  for (i = 0; i < 2; ++i) {
    side = (Bit) i;
    b = y->split[side];

    if (!b->split[oside])
    {
      join_BSTNode (y->joint, b, side_y);
      join_BSTNode (b, y->split[oside], oside);
      y->joint = b;
      y->split[side] = b->split[side];
      y->split[oside] = 0;
      return;
    }
  }

  /* We know both {0} and {3} exist.
   * {x} descends from {0} or {3} to be closest in value to {y}.
   * {b} follows one step behind {x}.
   **** OLD ********* NEW **** AUX ***
   *     y'            x        b
   *    / \           / \       |
   *   0   3         0   3      y
   *   .\.     -->   .\.         \
   *     b             b          *2
   *    / \           / \
   *  1*   x        1*   *2
   *      /
   *    2*
   */
  side = 0;  /* Arbitrary side.*/
  b = y->split[side];
  x = b->split[oside];
  do
  {
    b = x;
    x = b->split[oside];
  } while (x);
  x = b;
  b = x->joint;

  Claim2( oside ,==, side_of_BSTNode (x) );
  join_BSTNode (b, x->split[side], oside);

  x->joint = y->joint;
  x->joint->split[side_y] = x;
  join_BSTNode (x, y->split[0], 0);
  join_BSTNode (x, y->split[1], 1);

  y->joint = b;
  y->split[side] = 0;
  y->split[oside] = b->split[oside];
#undef oside
}

/** Do a tree rotation,
 *
 *       b             a
 *      / \           / \
 *     a   *z  -->  x*   b
 *    / \               / \
 *  x*   *y           y*   *z
 *
 * When /side/ is 1, opposite direction when 0.
 * (/b/ always starts as /a/'s joint)
 **/
  void
rotate_BSTNode (BSTNode* b, Bit side)
{
  const int p = side ? 0 : 1;
  const int q = side ? 1 : 0;
  BSTNode* a = b->split[p];
  BSTNode* y = a->split[q];

  join_BSTNode (b->joint, a, side_of_BSTNode (b));
  join_BSTNode (a, b, q);
  join_BSTNode (b, y, p);
}

#endif  /* #ifndef __OPENCL_VERSION__ */

