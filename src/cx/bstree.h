/**
 * \file bstree.h
 * Binary search tree.
 **/
#ifndef BSTree_H_
#ifndef __OPENCL_VERSION__
#define BSTree_H_

#include "def.h"
#endif

typedef struct BSTNode BSTNode;
typedef struct BSTree BSTree;

struct BSTNode
{
  BSTNode* joint;
  BSTNode* split[2];
};

struct BSTree
{
  BSTNode* sentinel;
#ifndef __OPENCL_VERSION__
  PosetCmp cmp;
#endif  /* #ifndef __OPENCL_VERSION__ */
};

#ifndef __OPENCL_VERSION__
BSTree
dflt2_BSTree (BSTNode* sentinel, PosetCmp cmp);
void
init_BSTree (BSTree* t, BSTNode* sentinel, PosetCmp cmp);
void
lose_BSTree (BSTree* t, void (* lose) (BSTNode*));

void
walk_BSTree (BSTree* t, Trit postorder,
    void (* f) (BSTNode*, void*), void* dat);
BSTNode*
find_BSTree (BSTree* t, const void* key);
void
insert_BSTree (BSTree* t, BSTNode* x);
BSTNode*
ensure_BSTree (BSTree* t, BSTNode* x);
BSTNode*
setf_BSTree (BSTree* t, BSTNode* x);
void
remove_BSTNode (BSTNode* y);
#endif  /* #ifndef __OPENCL_VERSION__ */

void
rotate_BSTNode (BSTNode* b, Bit side);

qual_inline
  BSTNode
dflt_BSTNode ()
{
  BSTNode a;
  a.joint = 0;  a.split[0] = 0;  a.split[1] = 0;
  return a;
}

qual_inline
  Bit
side_of_BSTNode (const BSTNode* x)
{
  return (x && x == x->joint->split[1]) ? 1 : 0;
}

qual_inline
  void
join_BSTNode (BSTNode* y, BSTNode* x, Bit side)
{
  if (y)  y->split[side] = x;
  if (x)  x->joint = y;
}

qual_inline
  void
plac_BSTNode (BSTNode* a, BSTNode* b)
{
  join_BSTNode (b->joint, a, side_of_BSTNode (b));
  join_BSTNode (a, b->split[0], 0);
  join_BSTNode (a, b->split[1], 1);
}

qual_inline
  BSTNode*
root_of_BSTree (BSTree* t)
{
  return t->sentinel->split[0];
}

qual_inline
  void
root_fo_BSTree (BSTree* t, BSTNode* x)
{
  x->joint = t->sentinel;
  t->sentinel->split[0] = x;
}

qual_inline
  bool
root_ck_BSTree (const BSTree* t, const BSTNode* x)
{
  return (x->joint == t->sentinel);
}


qual_inline
  BSTNode*
beg_BSTree (BSTree* t)
{
  BSTNode* x = root_of_BSTree (t);
  BSTNode* y = 0;

  while (x)
  {
    y = x;
    x = y->split[0];
  }
  return y;
}

qual_inline
  BSTNode*
next_BSTNode (BSTNode* x)
{
  if (x->split[1])
  {
    BSTNode* y;
    x = x->split[1];
    do
    {
      y = x;
      x = y->split[0];
    } while (x);
    return y;
  }

  while (x)
  {
    Bit side = side_of_BSTNode (x);
    x = x->joint;
    if (side == 0)
    {
      if (x->joint)  return x;
      return 0;
    }
  }
  return 0;
}

#endif

