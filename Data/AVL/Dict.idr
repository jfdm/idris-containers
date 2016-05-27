-- ---------------------------------------------------------------- [ Dict.idr ]
-- Module    : Dict.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| A Dictionary based upon an AVL Key-Value Tree.
module Data.AVL.Dict

import Data.AVL.Tree

%default total
%access export

data Dict : (k : Type) -> Type -> Type where
  MkDict : AVLTree h k v -> Dict k v

||| Empty
empty : (Ord k) => Dict k v
empty = MkDict (Element Empty AVLEmpty)

insert : (Ord k) => k -> v -> Dict k v -> Dict k v
insert key val (MkDict d) = MkDict $ snd (Tree.insert key val d)

||| Update the value for the given key.
update : (Ord k) => k -> (v -> v) -> Dict k v -> Dict k v
update x ufunc (MkDict d) = MkDict $ Tree.update x ufunc d

-- -------------------------------------------------------------------- [ List ]

toList : Dict k v -> List (k,v)
toList (MkDict d) = Tree.toList d

fromList : Ord k => List (k,v) -> Dict k v
fromList kvs = MkDict $ snd $ Tree.fromList kvs

-- ----------------------------------------------------------------- [ Queries ]

isEmpty : Dict k v -> Bool
isEmpty (MkDict d) = Tree.isEmpty d

foldr : (k -> v -> p -> p) -> p -> Dict k v -> p
foldr f init (MkDict d) = Tree.foldr f init d

lookup : (Ord k) => k -> Dict k v -> Maybe v
lookup k (MkDict d) = Tree.lookup k d

keys : Dict k v -> List k
keys (MkDict d) = Tree.keys d

values : Dict k v -> List v
values (MkDict d) = Tree.values d

size : Dict k v -> Nat
size (MkDict d) = Tree.size d

hasKey : (Ord k) => k -> Dict k v -> Bool
hasKey key (MkDict d) = Tree.hasKey key d

hasValue : (Eq v) => v -> Dict k v -> Bool
hasValue val (MkDict d) = Tree.hasValue val d

hasValueUsing : (v -> Bool) -> Dict k v -> Bool
hasValueUsing f (MkDict d) = Tree.any (\k,v => (f v)) d

findKey : (pred : v -> Bool) -> Dict k v -> Maybe k
findKey pred (MkDict d) = Tree.findKey pred d

findKeyOf : (Eq v) => v -> Dict k v -> Maybe k
findKeyOf v (MkDict d) = Tree.findKeyOf v d

-- --------------------------------------------------------- [ Implementations ]

(Eq k, Eq v) => Eq (Dict k v) where
   (==) (MkDict {h = h} x) (MkDict {h = h'} y) with (decEq h h')
     (==) (MkDict {h = h} x) (MkDict {h = h} y)  | Yes Refl = x == y
     (==) (MkDict {h = h} x) (MkDict {h = h'} y) | No _     = False

(Show k, Show v) => Show (Dict k v) where
  show (MkDict d) = show d

-- --------------------------------------------------------------------- [ EOF ]
