/**
 * \file associa.h
 * Associative array implementation.
 **/
#ifndef Associa_H_
#define Associa_H_
#include "lgtable.h"
#include "rbtree.h"

typedef struct Assoc Assoc;
typedef struct Associa Associa;

/** Associative array element (association).**/
struct Assoc
{
  RBTNode rbt;
};

/** Associative array.**/
struct Associa
{
  LgTable nodes;
  RBTree rbt;
  size_t key_sz;
  size_t val_sz;
  size_t assoc_offset;
  size_t key_offset;
  size_t val_offset;
};

/** Create a new associative array.
 * \param K  Type of key.
 * \param V  Type of value.
 * \param name  Name of variable to create.
 * \param cmp_fn  \ref PosetCmpFn which acts on keys.
 **/
#define InitAssocia( K, V, name, cmp_fn )  do \
{ \
  struct Assoc_Tmp \
  { \
    Assoc assoc; \
    K key; \
    V val; \
  }; \
  typedef struct Assoc_Tmp Assoc_Tmp; \
  name = cons7_Associa ((PosetCmpFn) cmp_fn, \
      sizeof(Assoc_Tmp), \
      sizeof(K), \
      sizeof(V), \
      offsetof( Assoc_Tmp, assoc ), \
      offsetof( Assoc_Tmp, key ), \
      offsetof( Assoc_Tmp, val )); \
} while (0)

#define InitSet( K, name, cmp_fn )  do \
{ \
  struct Assoc_Tmp \
  { \
    Assoc assoc; \
    K key; \
  }; \
  typedef struct Assoc_Tmp Assoc_Tmp; \
  name = cons7_Associa ((PosetCmpFn) cmp_fn, \
      sizeof(Assoc_Tmp), \
      sizeof(K), 0, \
      offsetof( Assoc_Tmp, assoc ), \
      offsetof( Assoc_Tmp, key ), 0);  \
} while (0)


/** Construct an associative array.
 * Don't use this directly.
 * \sa DeclAssocia()
 **/
qual_inline
  Associa
cons7_Associa (PosetCmpFn cmp_fn,
    size_t node_sz,
    size_t key_sz,
    size_t val_sz,
    size_t assoc_offset,
    size_t key_offset,
    size_t val_offset)
{
  Associa map;
  map.nodes = dflt1_LgTable (node_sz);
  map.key_sz       =  key_sz;
  map.val_sz       =  val_sz;
  map.assoc_offset =  assoc_offset;
  map.key_offset   =  key_offset;
  map.val_offset   =  val_offset;

  {
    void* node = take_LgTable (&map.nodes);
    Assoc* assoc = CastOff( Assoc, node ,+, map.assoc_offset );
    PosetCmp cmp;
    cmp.off = (ptrdiff_t) (key_offset - assoc_offset);
    cmp.fn = cmp_fn;
    map.rbt = dflt2_RBTree (&assoc->rbt, cmp);
  }
  return map;
}

/** Free everything.**/
qual_inline
  void
lose_Associa (Associa* map)
{
  lose_LgTable (&map->nodes);
}

/** Get the key of an association.**/
qual_inline
  void*
key_of_Assoc (Associa* map, Assoc* a)
{
  return (void*) ((size_t) a - map->assoc_offset + map->key_offset);
}

/** Get the value of an association.**/
qual_inline
  void*
val_of_Assoc (Associa* map, Assoc* a)
{
  return (void*) ((size_t) a - map->assoc_offset + map->val_offset);
}

/** Set the key for an association (don't use directly).
 * Only use this if the association is not in /really/ in the map.
 * That is, if it exists in the red-black tree.
 * \sa insert_Associa()
 **/
qual_inline
  void
key_fo_Assoc (Associa* map, Assoc* a, const void* key)
{
  void* p = key_of_Assoc (map, a);
  memcpy (p, key, map->key_sz);
}

/** Set the value for an association.**/
qual_inline
  void
val_fo_Assoc (Associa* map, Assoc* a, const void* val)
{
  void* p = val_of_Assoc (map, a);
  memcpy (p, val, map->val_sz);
}

/** Request a new element from the map.
 * I recommend not using this directly.
 * \sa insert_Associa()
 * \sa ensure_Associa()
 * \sa ensure1_Associa()
 **/
qual_inline
  Assoc*
take_Associa (Associa* map)
{
  void* node = take_LgTable (&map->nodes);
  Assoc* a = CastOff( Assoc, node ,+, map->assoc_offset );
  a->rbt.bst.joint = 0;
  return a;
}

/** Give an element back to the map.
 *
 * This is safe to use directly and will do all necessary node removal
 * from the underlying search data structure.
 *
 * \sa lose_Assoc()
 * \sa remove_Associa()
 **/
qual_inline
  void
give_Associa (Associa* map, Assoc* assoc)
{
  if (assoc->rbt.bst.joint)
    remove_RBTree (&map->rbt, &assoc->rbt);
  give_LgTable (&map->nodes, CastOff( void, assoc ,-, map->assoc_offset ));
}

/** Associate a key with a value in the map.
 * This can form duplicates.
 * \sa ensure_Associa()
 **/
qual_inline
  Assoc*
insert_Associa (Associa* map, const void* key, const void* val)
{
  Assoc* a = take_Associa (map);
  key_fo_Assoc (map, a, key);
  val_fo_Assoc (map, a, val);
  insert_RBTree (&map->rbt, &a->rbt);
  return a;
}

/** Find the association for the given key.
 * \return  NULL when the association could not be found.
 **/
qual_inline
  Assoc*
lookup_Associa (Associa* map, const void* key)
{
  BSTNode* bst = find_BSTree (&map->rbt.bst, key);

  if (!bst)  return 0;
  return CastUp( Assoc, rbt, CastUp( RBTNode, bst, bst ) );
}

/** Ensure an entry exists for the given key.
 * This will not cause duplicates.
 * \sa ensure_Associa()
 **/
qual_inline
  Assoc*
ensure1_Associa (Associa* map, const void* key, bool* added)
{
  Assoc* b = take_Associa (map);
  Assoc* a = 0;
  key_fo_Assoc (map, b, key);

  {
    RBTNode* rbt = ensure_RBTree (&map->rbt, &b->rbt);
    a = CastUp( Assoc, rbt, rbt );
  }
  /* If /b/ was added to the tree,
   * we must replace it with a node which is on the heap.
   */
  *added = (a == b);
  if (!*added)
    give_Associa (map, b);
  return a;
}

/** Ensure an entry exists for a given key.
 * This will not cause duplicates.
 * \sa ensure1_Associa()
 **/
qual_inline
  Assoc*
ensure_Associa (Associa* map, const void* key)
{
  bool added = false;
  return ensure1_Associa (map, key, &added);
}

/** Remove an association with the given key.
 * \sa give_Associa()
 **/
qual_inline
  void
remove_Associa (Associa* map, const void* key)
{
  Assoc* a = lookup_Associa (map, key);
  give_Associa (map, a);
}


/** Get the first association in the map.**/
qual_inline
  Assoc*
beg_Associa (Associa* map)
{
  BSTNode* bst = beg_BSTree (&map->rbt.bst);
  if (!bst)  return 0;
  return CastUp( Assoc, rbt, CastUp( RBTNode, bst, bst ) );
}

/** Get the next association in the map.**/
qual_inline
  Assoc*
next_Assoc (Assoc* a)
{
  BSTNode* bst = next_BSTNode (&a->rbt.bst);
  if (!bst)  return 0;
  return CastUp( Assoc, rbt, CastUp( RBTNode, bst, bst ) );
}


#endif

