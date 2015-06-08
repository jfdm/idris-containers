||| A Dependently Typed Implementation of an AVL Tree optimised for
||| Dictionaries.
|||
||| This code is dervied from an original design by David
||| Christiansen.
|||
||| *Note* When using this Data Structure, the design is such that the
||| tree does not factor in unbalanced trees and so removal of items is not permited.
module Data.AVL.Dependent.Dict

import Data.AVL.Dependent.Tree

%default total

data Dict' : (k : Type) -> Ord k -> Type -> Type where
  MkDict : {k : Type}
        -> {v : Type}
        -> AVLTree h k o v
        -> Dict' k o v

Dict : (k : Type) -> {default %instance o : Ord k} -> (v : Type) -> Type
Dict k {o = o} v = Dict' k o v

||| Empty
empty : (o : Ord k) => Dict k {o = o} v
empty = MkDict (Element Empty AVLEmpty)

insert : (o : Ord k) => k -> v -> Dict k {o = o} v -> Dict k {o = o} v
insert key val (MkDict d) = MkDict $ Sigma.getProof (runInsertRes $ Tree.insert key val d)

||| Update the value for the given key.
update : (o : Ord k) => k -> (v -> v) -> Dict k {o = o} v -> Dict k {o = o} v
update x ufunc (MkDict d) = MkDict $ Tree.update x ufunc d

-- -------------------------------------------------------------------- [ List ]

toList : Dict k {o = o} v -> List (k,v)
toList (MkDict d) = Tree.toList d

fromList : Ord k => List (k,v) -> Dict k v
fromList kvs = MkDict $ Sigma.getProof $ Tree.fromList kvs


-- ----------------------------------------------------------------- [ Queries ]

lookup : (o : Ord k) => k -> Dict k {o = o} v -> Maybe v
lookup k (MkDict d) = Tree.lookup k d

keys : Dict k {o = o} v -> List k
keys (MkDict d) = Tree.keys d

values : Dict k {o = o} v -> List v
values (MkDict d) = Tree.values d

size : Dict k {o = o} v -> Nat
size (MkDict d) = Tree.size d

hasKey : k -> Dict k {o = o} v -> Bool
hasKey key (MkDict d) = Tree.hasKey key d

hasValue : (Eq v) => v -> Dict k {o = o} v -> Bool
hasValue val (MkDict d) = Tree.hasValue val d

findKey : (pred : v -> Bool) -> Dict k {o = o} v -> Maybe k
findKey pred (MkDict d) = Tree.findKey pred d

findKeyOf : (Eq v) => v -> Dict k {o = o} v -> Maybe k
findKeyOf v (MkDict d) = Tree.findKeyOf v d

instance (Eq k, Eq v) => Eq (Dict k {o = o} v) where
   (==) (MkDict {h = h} x) (MkDict {h = h'} y) with (decEq h h')
     (==) (MkDict {h = h} x) (MkDict {h = h} y)  | Yes Refl = x == y
     (==) (MkDict {h = h} x) (MkDict {h = h'} y) | No _     = False

instance (Show k, Show v) => Show (Dict k {o = o} v) where
  show (MkDict d) = show d

-- --------------------------------------------------------------------- [ EOF ]
