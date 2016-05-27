-- ----------------------------------------------------------------- [ Set.idr ]
-- Module    : Set.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Implementation of a Set using an AVL Binary Search Tree.
module Data.AVL.Set

import Data.AVL.Tree

%access export

-- ------------------------------------------------------------- [ Definitions ]
||| An ordered set.
data Set : (a : Type) -> Type where
  MkSet : {a : Type} -> AVLTree n a Unit -> Set a

||| Return a empty set.
empty : (Ord a) => Set a
empty = MkSet (Element Empty AVLEmpty)

||| Insert an element into a set.
insert : (Ord a) => a -> Set a -> Set a
insert a (MkSet m) = MkSet (snd $ Tree.insert a () m)

||| Does the set contain the given element.
contains : (Ord a) => a -> Set a -> Bool
contains a (MkSet m) = isJust (lookup a m)

||| Construct a set that contains all elements in both of the input sets.
union : (Ord a) => Set a -> Set a -> Set a
union (MkSet m1) (MkSet m2) = MkSet (snd $ Tree.foldr insertElement (_ ** m1) m2)
  where
    insertElement : (Ord a) => a
                            -> Unit
                            -> (h : Nat ** AVLTree h a Unit)
                            -> (h' : Nat ** AVLTree h' a Unit)
    insertElement k v m' = Tree.insert k v (snd m')

||| Return the size of the Dictionary.
size : Set a -> Nat
size (MkSet m) = Tree.size m

||| Construct a set that contains the elements from the first input
||| set but not the second.
|||
||| *Note* Not an efficient operation as we are constructing a new set
||| instead of modifying the right one.
difference : (Ord a) => Set a -> Set a -> Set a
difference (MkSet m1) s2 = Tree.foldr (\e,_,t => if (contains e s2) then t else Set.insert e t) empty $ m1

||| Construct a set that contains common elements of the input sets.
intersection : (Ord a) => Set a -> Set a -> Set a
intersection s1 s2 = difference s1 (difference s1 s2)

||| Construct a list using the given set.
toList : Set a -> List a
toList (MkSet m) = map fst $ Tree.toList m

||| Construct a set from the given list.
fromList : (Ord a) => List a -> Set a
fromList xs = (foldl (\t,k => Set.insert k t) empty xs)

-- --------------------------------------------------------- [ Implementations ]
Foldable Set where
  foldr f i (MkSet m) = foldr (\x,_,p => f x p) i m

Eq a => Eq (Set a) where
  (==) (MkSet (Element t _)) (MkSet (Element t' _)) = t == t'

Show a => Show (Set a) where
  show s = "{ " ++ (unwords . intersperse "," . map show . Set.toList $ s) ++ " }"
-- --------------------------------------------------------------------- [ EOF ]
