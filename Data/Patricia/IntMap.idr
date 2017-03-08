-- --------------------------------------------------------------- [ IntMap.idr ]
-- Module    : IntMap.idr
-- Copyright : (c) 2017 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Dependently type implementation of an Integer Map based on
||| _big-endian_ Patricia trees. Dependent types are used to encode
||| bit size of keys and to enforce some invariants for data structure.
|||
||| Algorithm is taken from Chris Okasaki and Andy Gill,
||| "Fast Mergeable Integer Maps", Workshop on ML, September 1998, pages 77-86.
||| Some implementation details are taken from
||| [Haskell implementation](http://hackage.haskell.org/package/containers-0.5.10.1/docs/Data-IntMap.html).
|||
||| Most functions have `O(min(n, W))` running time, where `n` is number of elements
||| and `W` is size of bits to store key.
module Data.Patricia.IntMap

import Data.Bits
import Data.Fin

import Data.Patricia.BitsUtils

%default total
%access export

||| The core patricia tree data structure used to represent integer key-value map.
|||
||| @bits  Number of bits in `key`.
||| @valTy The type associated with the value.
public export
data IntBitMap : (bits : Nat) -> (valTy : Type) -> Type where
    ||| An empty `IntBitMap` node.
    Empty : IntBitMap (S n) v

    ||| A Leaf node in the Tree.
    |||
    ||| @n     Number of bits in key.
    ||| @key   The key: integer of `n` bits.
    ||| @val   The value associated with the key.
    Leaf : (key : Bits (S n))
        -> (val : v)
        -> IntBitMap (S n) v

    ||| A binary node in the tree.
    |||
    ||| *Invariant:* `Empty` is never found as a child of `Bin`. TODO: encode this
    |||
    ||| @n     Number of bits in key.
    ||| @pref  The common high-order bits that all elements share to the left of the `brBit` bit.
    |||        Bit at `brBit` is set to `0` and all the lesser bits to `1`.
    ||| @brBit The largest bit position in `pref` at which two elements of the set differ.
    ||| @left  The left child of the Binary Node.
    ||| @right The right child of the Binary Node.
    Bin : (pref  : Bits (S n))
       -> (brBit : Fin (S n))
       -> (left  : IntBitMap (S n) v)
       -> (right : IntBitMap (S n) v)
       -> IntBitMap (S n) v

%name IntBitMap t, tree

Functor (IntBitMap (S n)) where
    map f = mapGo where
      mapGo : IntBitMap (S n) a -> IntBitMap (S n) b
      mapGo Empty                       = Empty
      mapGo (Leaf key val)              = Leaf key (f val)
      mapGo (Bin pref brBit left right) = Bin pref brBit (mapGo left) (mapGo right)

Foldable (IntBitMap (S n)) where
    foldr f init = go init where
      go : acc -> IntBitMap (S n) elem -> acc
      go acc Empty                = acc
      go acc (Leaf _ val)         = f val acc
      go acc (Bin _ _ left right) = go (go acc right) left

||| Integer map with 32 bits integers as a key.
public export
Int32Map : (valTy : Type) -> Type
Int32Map v = IntBitMap 32 v

||| `O(n)`. Number of elements in `IntBitMap`.
size : IntBitMap (S n) v -> Nat
size Empty = 0
size (Leaf _ _) = 1
size (Bin _ _ left right) = size left + size right

||| `O(min(n, W))`. Lookup the value at a key in the `IntBitMap`.
public export
lookup : Integer -> IntBitMap (S n) v -> Maybe v
lookup {n} key t with (intToBits {n=S n} key)
  lookup {n} key t | bitKey = go t where
    go : IntBitMap (S n) v -> Maybe v
    go Empty = Nothing
    go (Leaf treeKey val) = if treeKey == bitKey then Just val else Nothing
    go (Bin pref _ left right) = if bitKey <= pref  -- we can compare `key` with `pref` because of BE patricia trees
                                 then go left
                                 else go right

||| `O(W)`. Joins two nodes into one tree, creating `Bin` node.
||| Both nodes should be not `Empty`.
private
joinNodes : IntBitMap (S n) v -> IntBitMap (S n) v -> IntBitMap (S n) v
joinNodes Empty _ = Empty  -- TODO: ensure at compile time
joinNodes _ Empty = Empty  -- TODO: ensure at compile time
joinNodes {n} t1 t2 = let bBit     = branchingBit pref1 pref2
                          prefMask = maskInsignificant bBit pref1
                      in if isZeroBit bBit pref1
                         then Bin prefMask bBit t1 t2
                         else Bin prefMask bBit t2 t1
  where
    pref : IntBitMap (S n) v -> Bits (S n)
    pref Empty = cast 0  -- TODO: ensure this never happens
    pref (Leaf key _) = key
    pref (Bin p _ _ _) = p

    pref1 : Bits (S n)
    pref1 = pref t1

    pref2 : Bits (S n)
    pref2 = pref t2

||| `O(min(n,W))`. Insert a new `(key,value)` pair in the `IntBitMap`.
||| If the key is already present in the map, the associated value is
||| replaced with the supplied value.
insert : Integer -> v -> IntBitMap (S n) v -> IntBitMap (S n) v
insert {n} key val t with (intToBits {n=S n} key)
  insert {n} key val t | bitKey = go t where
    go : IntBitMap (S n) v -> IntBitMap (S n) v
    go Empty = Leaf bitKey val

    go lf@(Leaf oldKey oldVal) =
        if oldKey == bitKey
        then Leaf bitKey val
        else joinNodes lf (Leaf bitKey val)

    go br@(Bin pref brBit left right) =
        if matchPrefix brBit pref bitKey
        then if isZeroBit brBit bitKey  -- bitKey <= pref
             then Bin pref brBit (go left) right
             else Bin pref brBit left (go right)
        else joinNodes br (Leaf bitKey val)

-- λΠ> the (Int32Map String) $ insert 3 "a" Empty
-- Leaf (MkBits 3) "a" : IntBitMap 32 String
-- λΠ> the (Int32Map String) $ insert 2 "c" $ insert 4 "b" $ insert 3 "a" Empty
-- Bin (MkBits 3)
--     (FS (FS FZ))
--     (Bin (MkBits 2) FZ (Leaf (MkBits 2) "c") (Leaf (MkBits 3) "a"))
--     (Leaf (MkBits 4) "b") : IntBitMap 32 String
-- λΠ> toList $ the (Int32Map String) $ insert 2 "c" $ insert 4 "b" $ insert 3 "a" Empty
-- Can't find implementation for Foldable Int32Map
-- λΠ> toList $ the (IntBitMap 32 String) $ insert 2 "c" $ insert 4 "b" $ insert 3 "a" Empty
-- ["c", "a", "b"] : List String
