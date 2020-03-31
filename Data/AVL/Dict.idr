-- ---------------------------------------------------------------- [ Dict.idr ]
-- Module    : Dict.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| A Dictionary based upon an AVL Key-Value AVL.API.
module Data.AVL.Dict

import public Data.Tree
import public Data.AVL.Core
import public Data.AVL.Core.API
import public Data.AVL.Core.Quantifiers

%default total
%access public export

data Dict : (k : Type) -> Type -> Type where
  MkDict : AVLTree h k v -> Dict k v

||| Empty
empty : (Ord k) => Dict k v
empty = MkDict (Element Empty AVLEmpty)

insert : (Ord k) => k -> v -> Dict k v -> Dict k v
insert key val (MkDict d) = MkDict $ snd (insert key val d)

||| Update the value for the given key.
update : (Ord k) => k -> (v -> v) -> Dict k v -> Dict k v
update x ufunc (MkDict d) = MkDict $ update x ufunc d

-- -------------------------------------------------------------------- [ List ]

toList : Dict k v -> List (k,v)
toList (MkDict d) = toList d

fromList : Ord k => List (k,v) -> Dict k v
fromList kvs = MkDict $ snd $ fromList kvs

-- ----------------------------------------------------------------- [ Queries ]

isEmpty : Dict k v -> Bool
isEmpty (MkDict d) = isEmpty d

foldr : (k -> v -> p -> p) -> p -> Dict k v -> p
foldr f init (MkDict d) = foldr f init d

lookup : (Ord k) => k -> Dict k v -> Maybe v
lookup k (MkDict d) = lookup k d

keys : Dict k v -> List k
keys (MkDict d) = keys d

values : Dict k v -> List v
values (MkDict d) = values d

size : Dict k v -> Nat
size (MkDict d) = size d

hasKey : (Ord k) => k -> Dict k v -> Bool
hasKey key (MkDict d) = hasKey key d

hasValue : (Eq v) => v -> Dict k v -> Bool
hasValue val (MkDict d) = hasValue val d

hasValueUsing : (v -> Bool) -> Dict k v -> Bool
hasValueUsing f (MkDict d) = any (\k,v => (f v)) d

findKey : (pred : v -> Bool) -> Dict k v -> Maybe k
findKey pred (MkDict d) = findKey pred d

findKeyOf : (Eq v) => v -> Dict k v -> Maybe k
findKeyOf v (MkDict d) = findKeyOf v d

-- --------------------------------------------------------- [ Implementations ]

(Eq k, Eq v) => Eq (Dict k v) where
   (==) (MkDict {h = h} x) (MkDict {h = h'} y) with (decEq h h')
     (==) (MkDict {h = h} x) (MkDict {h = h} y)  | Yes Refl = x == y
     (==) (MkDict {h = h} x) (MkDict {h = h'} y) | No _     = False

(Show k, Show v) => Show (Dict k v) where
  show (MkDict d) = show d

Ord a => Functor (Dict a) where
  map func x = fromList $ (\(a, b) => (a, func b)) <$> toList x

Ord a => Foldable (Dict a) where
  foldr func = foldr $ const func

Ord a => Traversable (Dict a) where
  traverse f x = fromList <$> (traverse (\(a, b) => (MkPair a) <$> f b) $ Dict.toList x)

namespace Predicates

  data HasKey : (key  : typeKey)
             -> (dict : Dict typeKey typeValue)
             -> Type
    where
      IsKey : (prf : HasKey key tree)
           -> HasKey key (MkDict tree)

  keyNotInDict : (contra : HasKey key tree -> Void)
              -> HasKey key (MkDict tree)
              -> Void
  keyNotInDict contra (IsKey x) = contra x

  isKey : DecEq typeKey
       => (key  : typeKey)
       -> (dict : Dict typeKey typeValue)
       -> Dec (HasKey key dict)
  isKey key (MkDict tree) with (isKey key tree)
    isKey key (MkDict tree) | (Yes x) = Yes (IsKey x)
    isKey key (MkDict tree) | (No contra) = No (keyNotInDict contra)

  data HasValue : (value : typeValue)
               -> (dict  : Dict typeKey typeValue)
               -> Type
    where
      IsValue : (prf : HasValue value tree)
             -> HasValue value (MkDict tree)

  valueNotInDict : (contra : HasValue value tree -> Void)
                -> HasValue value (MkDict tree)
                -> Void
  valueNotInDict contra (IsValue prf) = contra prf

  isValue : DecEq typeValue
         => (value : typeValue)
         -> (dict  : Dict typeKey typeValue)
         -> Dec (HasValue value dict)
  isValue value (MkDict tree) with (isValue value tree)
    isValue value (MkDict tree) | (Yes x) = Yes (IsValue x)
    isValue value (MkDict tree) | (No contra) = No (valueNotInDict contra)

-- --------------------------------------------------------------------- [ EOF ]
