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
module Data.Patricia.IntMap

import Data.Bits
import Data.Fin

%default total
%access export

||| The core tree key-value data structure used to represent an AVL
||| Tree.
|||
||| This structure doesn't encode the invariants of the tree and is
||| *simply* a container. This structure ideally shouldn't be exposed
||| to the user at all. This structure should be used to build other
||| data structures.  See the modules alongside this for appropriate
||| interfaces for using the tree.
|||
||| @bits  Number of bits in `key`.
||| @valTy The type associated with the value.
public export
data IntBitMap : (bits : Nat) -> (valTy : Type) -> Type where
    ||| An empty `IntBitMap` node.
    Empty : IntBitMap n v

    ||| A Leaf node in the Tree.
    |||
    ||| @n     Number of bits in key.
    ||| @key   The key: integer of `n` bits.
    ||| @val   The value associated with the key.
    Leaf : (key : Bits n)
        -> (val : v)
        -> IntBitMap n v

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
    Bin : (pref  : Bits n)
       -> (brBit : Fin n)
       -> (left  : IntBitMap n v)
       -> (right : IntBitMap n v)
       -> IntBitMap n v

%name IntBitMap t, tree
