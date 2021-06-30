/**
 * \file rbtree.c
 * Red-black tree.
 **/
#include "rbtree.h"
#include <stdlib.h>

  static Bit
root (const RBTree* t, const RBTNode* x)
{
  return root_ck_BSTree (&t->bst, &x->bst);
}

  static RBTNode*
joint (RBTNode* x)
{
  return CastUp( RBTNode, bst, x->bst.joint );
}

  static RBTNode*
split (RBTNode* x, Bit side)
{
  BSTNode* y = x->bst.split[side];
  return y ? CastUp( RBTNode, bst, y ) : 0;
}

  static void
rotate (RBTNode* x, Bit lowup)
{
  rotate_BSTNode (&x->bst, lowup);
}

  RBTree
dflt2_RBTree (RBTNode* sentinel, PosetCmp cmp)
{
  RBTree t;
  sentinel->red = 0;
  cmp = dflt3_PosetCmp (offsetof(RBTNode, bst), cmp.off, cmp.fn);
  t.bst = dflt2_BSTree (&sentinel->bst, cmp);
  return t;
}

  void
init_RBTree (RBTree* t, RBTNode* sentinel, PosetCmp cmp)
{
  *t = dflt2_RBTree (sentinel, cmp);
}

  static void
fixup_insert (RBTNode* x, RBTree* t)
{
  while (1)
  {
    RBTNode* b;
    RBTNode* a;
    Bit xside;

    /* /x/ is root, just set to black!*/
    if (root (t, x))
    {
      x->red = Nil;
      break;
    }
    b = joint (x);

    /* /b/ is black, /x/ is safe to be red!*/
    if (!b->red)  break;

    a = joint (b);
    xside = side_of_BSTNode (&x->bst);

    /* Case 1.         (continue)
     *
     *    a#              b'+
     *    / \              / \
     *  1*   +b          a#   #x
     *      / \          /|   |\
     *    2#   +'x     w* #2 3# #4
     *        / \
     *      3#   #4
     */
    if (xside == side_of_BSTNode (&b->bst))
    {
      rotate (a, !xside);
      x->red = Nil;
      x = b;
    }
    /* Case 2.                       (continue)
     *
     *       a#             a#          b'+
     *       / \            / \          / \
     *     b+   *4   =>   x+   *4  =>  x#   #a
     *     / \            / \          /|   |\
     *   1#   +'x       b#   #3      1# #2 3# *4
     *       / \        / \
     *     2#   #3    1#   #2
     */
    else
    {
      rotate (b, !xside);
      b->red = Nil;
      rotate (a, xside);
    }
  }
}

  void
insert_RBTree (RBTree* t, RBTNode* x)
{
  insert_BSTree (&t->bst, &x->bst);
  x->red = Yes;
  fixup_insert (x, t);
}

/** If a node matching /x/ exists, return that node.
 * Otherwise, add /x/ to the tree and return it.
 **/
  RBTNode*
ensure_RBTree (RBTree* t, RBTNode* x)
{
  BSTNode* y = ensure_BSTree (&t->bst, &x->bst);
  if (y == &x->bst)
  {
    x->red = Yes;
    fixup_insert (x, t);
  }
  else
  {
    x = CastUp( RBTNode, bst, y );
  }
  return x;
}

/**
 * Ensure /x/ exists in the tree.
 * It replaces a matching node if one exists.
 * The matching node (which was replaced) is returned.
 * If no matching node was replaced, 0 is returned.
 **/
  RBTNode*
setf_RBTree (RBTree* t, RBTNode* x)
{
  BSTNode* y = setf_BSTree (&t->bst, &x->bst);
  if (!y)  return 0;
  x->red = Yes;
  fixup_insert (x, t);
  return CastUp( RBTNode, bst, y );
}

/**
 * This function is called with {y} removed from the tree,
 * but {y->joint} points to a node whose {side} is one level
 * short on black nodes.
 **/
  static void
fixup_remove (RBTNode* y, RBTree* t, Bit side)
{
  if (y->red)
  {
    y->red = 0;
    return;
  }

  while (!root (t, y))
  {
    RBTNode* b = joint (y);
    RBTNode* a = split (b, !side);
    RBTNode* w = split (a, !side);
    RBTNode* x = split (a, side);

    /* Case 1.                         (done)
     *
     *      b*             b*            x*
     *      / \            / \           / \
     *    a#   #'y  -->  x+   #y  -->  a#   #b
     *    / \            / \           /|   |\
     *  w*   +x        a#   #2       w* #1 2# #y
     *       / \       / \
     *     1#   #2   w*   #1
     */
    if (x && x->red)
    {
      rotate (a, !side);
      rotate (b, side);
      if (b->red)  b->red = 0;
      else         x->red = 0;
      break;
    }

    /* Case 2.           (done)
     *
     *      b+             a#
     *      / \            / \
     *    a#   #'y  -->  w*   +b
     *    / \                / \
     *  w*   #x            x#   #y
     */
    if (b->red)
    {
      rotate (b, side);
      break;
    }

    /* Case 3.         (continue, match case 1 or 2)
     *
     *      b#             a#
     *      / \            / \
     *    a+   #'y  -->  w#   +b
     *    / \                / \
     *  w#   #x            x#   #'y
     */
    if (a->red)
    {
      rotate (b, side);
      a->red = 0;
      b->red = 1;
      continue;  /* Match case 1 or 2.*/
    }

    /* Case 4.           (done)
     *
     *      b#             a#
     *      / \            / \
     *    a#   #'y  -->  w#   #b
     *    / \                / \
     *  w+   *x            x*   #y
     */
    if (w && w->red)
    {
      rotate (b, side);
      w->red = 0;
      break;
    }

    /* Case 5.         (continue)
     *
     *      b#            b'#
     *      / \            / \
     *    a#   #'y  -->  a+   #y
     *    / \            / \
     *  w#   #x        w#   #x
     */
    a->red = 1;
    y = b;
    side = side_of_BSTNode (&y->bst);
  }
}

  void
remove_RBTree (RBTree* t, RBTNode* y)
{
  RBTNode* b = joint (y);
  RBTNode* z;
  Bit side = side_of_BSTNode (&y->bst);
  remove_BSTNode (&y->bst);
  z = split (b, side);
  if (z) {
    /* Recolor the node that replaced {y}.*/
    SwapT( uint, y->red, z->red );
  }

  /* If the removed color is red, then it is still a red-black tree.*/
  if (y->red)  return;

  if (y->bst.split[0]) {
    fixup_remove (split (y, 0), t, 0);
  }
  else if (y->bst.split[1]) {
    fixup_remove (split (y, 1), t, 1);
  }
  else {
    /* Assume {y} is a leaf in the tree to simplify fixup.*/
    fixup_remove (y, t, !y->bst.joint->split[1]);
  }
}

