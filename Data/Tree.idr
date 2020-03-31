module Data.Tree

%default total
%access public export

||| A key-value tree data structure.
|||
||| This structure doesn't encode the invariants of the tree and is
||| *simply* a container. This structure ideally shouldn't be exposed
||| to the user at all. This structure should be used to build other
||| data structures.  See the modules alongside this for appropriate
||| interfaces for using the tree.
|||
||| @keyTy The type associated with the key.
||| @valTy The type associated with the value.
data Tree : (keyTy : Type)
         -> (valTy : Type)
         -> Type
  where
    ||| An empty Tree node.
    Empty : Tree k v

    ||| A Key Value node in the Tree.
    |||
    ||| @key   The key.
    ||| @val   The value associated with the key.
    ||| @left  The left child of the Node
    ||| @right THe right child of the Node.
    Node : (key   : k)
        -> (val   : v)
        -> (left  : Tree k v)
        -> (right : Tree k v)
        -> Tree k v

%name Tree t, tree

namespace Keys

  ||| A proof that some key is found in a Tree
  data IsKeyIn : k -> Tree k v -> Type where
    Here : IsKeyIn key (Node key _ _ _)
    InRight : (later : IsKeyIn key r) -> IsKeyIn key (Node not_key _ _ r)
    InLeft :  (later : IsKeyIn key l) -> IsKeyIn key (Node not_key _ l _)


  ||| An empty tree has no key
  emptyTreeHasNoKey : {key : k} -> IsKeyIn key Empty -> Void
  emptyTreeHasNoKey Here impossible
  emptyTreeHasNoKey (InRight _) impossible
  emptyTreeHasNoKey (InLeft _) impossible

  Uninhabited (IsKeyIn key Empty) where
    uninhabited = emptyTreeHasNoKey

  ||| An item that is not in the root, not in the left child and not in the
  ||| right child is not in the Tree at all
  noKeyFound : {key : k}
            -> {val : v}
            -> {key' : k}
            -> {l : Tree k v}
            -> {r : Tree k v}
            -> Not (key = key')
            -> Not (IsKeyIn key l)
            -> Not (IsKeyIn key r)
            -> Not (IsKeyIn key (Node key' val l r))
  noKeyFound notHere notInLeft notInRight Here = notHere Refl
  noKeyFound notHere notInLeft notInRight (InLeft later) = notInLeft later
  noKeyFound notHere notInLeft notInRight (InRight later) = notInRight later

  ||| A decision procedure for Key
  isKey : DecEq k
       => (key : k)
       -> (tree : Tree k v)
       -> Dec (IsKeyIn key tree)
  isKey key Empty = No emptyTreeHasNoKey
  isKey key (Node key' _ l r) with (decEq key key')
    isKey key (Node key  _ l r) | (Yes Refl) = Yes Here
    isKey key (Node key' _ l r) | (No notHere) with (isKey key l)
      isKey key (Node key' _ l r) | (No notHere) | (Yes inLeft) = Yes (InLeft inLeft)
      isKey key (Node key' _ l r) | (No notHere) | (No notInLeft) with (isKey key r)
        isKey key (Node key' _ l r) | (No notHere) | (No notInLeft) | (Yes inRight) = Yes (InRight inRight)
        isKey key (Node key' _ l r) | (No notHere) | (No notInLeft) | (No notInRight) = No (noKeyFound notHere notInLeft notInRight)

  public export
  data All : (predicate : typeKey -> Type)
          -> (tree      : Tree typeKey typeValue)
          -> Type
    where
      Leaf : All p Empty
      Node : (prf : p key)
          -> (leftBranch  : All p left)
          -> (rightBranch : All p right)
          -> All p (Node key _ left right)


namespace Values
  public export
  data IsValueIn : (value : typeValue)
                -> (tree  : Tree typeKey typeValue)
                -> Type
    where
      Here    : IsValueIn value (Node _ value _ _)
      InRight : (later : IsValueIn value r) -> IsValueIn value (Node _ not_value _ r)
      InLeft  : (later : IsValueIn value l) -> IsValueIn value (Node _ not_value l _)

  emptyTreeHasNoValue : IsValueIn value Empty -> Void
  emptyTreeHasNoValue Here impossible
  emptyTreeHasNoValue (InRight _) impossible
  emptyTreeHasNoValue (InLeft _) impossible

  Uninhabited (IsValueIn value Empty) where
    uninhabited Here impossible
    uninhabited (InRight _) impossible
    uninhabited (InLeft _) impossible

  ||| A decision procedure for Value
  valueNotFound : (notHere : (value = val) -> Void)
               -> (isNotLeft : IsValueIn value left -> Void)
               -> (isNotRight : IsValueIn value right -> Void)
               -> IsValueIn value (Node key val left right)
               -> Void
  valueNotFound notHere isNotLeft isNotRight Here = notHere Refl
  valueNotFound notHere isNotLeft isNotRight (InRight later) = isNotRight later
  valueNotFound notHere isNotLeft isNotRight (InLeft later) = isNotLeft later

  isValue : DecEq typeValue
         => (value : typeValue)
         -> (tree : Tree typeKey typeValue)
         -> Dec (IsValueIn value tree)
  isValue value Empty = No emptyTreeHasNoValue
  isValue value (Node key val left right) with (decEq value val)
    isValue val (Node key val left right) | (Yes Refl) = Yes Here
    isValue value (Node key val left right) | (No notHere) with (isValue value left)
      isValue value (Node key val left right) | (No notHere) | (Yes prf) = Yes (InLeft prf)
      isValue value (Node key val left right) | (No notHere) | (No isNotLeft) with (isValue value right)
              isValue value (Node key val left right) | (No notHere) | (No isNotLeft) | (Yes prf) = Yes (InRight prf)
              isValue value (Node key val left right) | (No notHere) | (No isNotLeft) | (No isNotRight) = No (valueNotFound notHere isNotLeft isNotRight)

  public export
  data All : (predicate : typeValue -> Type)
          -> (tree      : Tree typeKey typeValue)
          -> Type
    where
      Leaf : Values.All p Empty
      Node : (prf : p value)
          -> (leftBranch  : Values.All p left)
          -> (rightBranch : Values.All p right)
          -> Values.All p (Node _ value left right)


namespace KVPairs
  public export
  data All : (predicate : typeKey -> typeValue -> Type)
          -> (tree      : Tree typeKey typeValue)
          -> Type
    where
      Leaf : KVPairs.All p Empty
      Node : (prf : p key value)
          -> (leftBranch  : KVPairs.All p left)
          -> (rightBranch : KVPairs.All p right)
          -> KVPairs.All p (Node key value left right)
