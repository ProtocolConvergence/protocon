/**
 * \file rbtree.h
 * Red-black tree.
 **/
#ifndef RBTree_H_
#define RBTree_H_
#include "bstree.h"

typedef struct RBTNode RBTNode;
typedef struct RBTree  RBTree;

struct RBTNode
{
  BSTNode bst;
  Bit red;
};

struct RBTree
{
  BSTree bst;
};

RBTree
dflt2_RBTree (RBTNode* sentinel, PosetCmp cmp);
void
init_RBTree (RBTree* t, RBTNode* sentinel, PosetCmp cmp);
void
insert_RBTree (RBTree* t, RBTNode* x);
RBTNode*
ensure_RBTree (RBTree* t, RBTNode* x);
RBTNode*
setf_RBTree (RBTree* t, RBTNode* x);
void
remove_RBTree (RBTree* t, RBTNode* y);

qual_inline
  void
plac_RBTNode (RBTNode* a, RBTNode* b)
{
  if (a)  a->red = b->red;
  plac_BSTNode (&a->bst, &b->bst);
}

#endif

