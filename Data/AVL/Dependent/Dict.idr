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

data Dict : Type -> Type -> Type where
  MkDict : {k : Type}
        -> {v : Type}
        -> {default %instance o : Ord k}
        -> Tree h k o v
        -> Dict k v

||| Empty
empty : Ord k => Dict k v
empty = MkDict Empty

partial
insert : Ord k => k -> v -> Dict k v -> Dict k v
insert key val (MkDict d) =
  case Tree.insert key val d of
    Grew x => MkDict x
    Same x => MkDict x


||| Update the value for the given key.
partial
update : Ord k => k -> (v -> v) -> Dict k v -> (Dict k v)
update x ufunc (MkDict d) = case updateValueBy (compare x) ufunc d of
  Same x => MkDict x

-- -------------------------------------------------------------------- [ List ]

toList : Dict k v -> List (k,v)
toList (MkDict d) = Tree.toList d

fromList : Ord k => List (k,v) -> Dict k v
fromList kvs = MkDict $ Sigma.getProof $ Tree.fromList kvs


-- ----------------------------------------------------------------- [ Queries ]

lookupUsing : Ord k => (k -> Ordering) -> Dict k v -> Maybe v
lookupUsing f (MkDict d) = Tree.lookupUsing f d

lookup : Ord k => k -> Dict k v -> Maybe v
lookup k (MkDict d) = Tree.lookup k d

isKey : Ord k => k -> Dict k v -> Bool
isKey k (MkDict d) = Tree.isKey k d

keys : Ord k => Dict k v -> List k
keys (MkDict d) = Tree.keys d

values : Ord k => Dict k v -> List v
values (MkDict d) = Tree.values d

length : Ord k => Dict k v -> Nat
length (MkDict d) = Tree.length d

hasKeyUsing : (Ord k) => (k -> Ordering) -> Dict k v -> Bool
hasKeyUsing f (MkDict d) = Tree.hasKeyUsing f d

hasKey : (Ord k) => k -> Dict k v -> Bool
hasKey key (MkDict d) = Tree.hasKey key d

hasValueUsing : Ord k => (v -> Bool) -> Dict k v -> Bool
hasValueUsing f (MkDict d) = Tree.hasValueUsing f d

hasValue : (Ord k, Eq v) => v -> Dict k v -> Bool
hasValue val (MkDict d) = Tree.hasValue val d

getKeyUsing : Ord k => (v -> Bool) -> Dict k v -> Maybe k
getKeyUsing f (MkDict d) = Tree.getKeyUsing f d

getKey : (Ord k, Eq v) => v -> Dict k v -> Maybe k
getKey v (MkDict d) = Tree.getKey v d

instance (Eq k, Eq v) => Eq (Dict k v) where
   (==) (MkDict x) (MkDict y) = Tree.eqTree x y

instance (Show k, Show v) => Show (Dict k v) where
  show (MkDict d) = show d

-- --------------------------------------------------------------------- [ EOF ]
