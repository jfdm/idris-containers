||| Implementation of a Set using an AVL Binary Search Tree.
module Data.AVL.Dependent.Set

import Data.AVL.Dependent.Tree

data Set' : (a : Type) -> Ord a -> Type where
  MkSet : {a : Type} -> AVLTree n a o Unit -> Set' a o

Set : (a : Type) -> {default %instance o : Ord a} -> Type
Set a {o = o} = Set' a o

||| Return a empty set.
empty : (o : Ord a) => Set {o = o} a
empty = MkSet (Element Empty AVLEmpty)

||| Insert an element into a set.
insert : (o : Ord a) => a -> Set {o = o} a -> Set {o = o} a
insert a (MkSet m) = MkSet (Sigma.getProof $ runInsertRes (Tree.insert a () m))

||| Does the set contain the given element.
contains : (o : Ord a) => a -> Set {o = o} a -> Bool
contains a (MkSet m) = isJust (lookup a m)

||| Construct a set that contains all elements in both of the input sets.
union : (o : Ord a) => Set {o = o} a -> Set {o = o} a -> Set {o = o} a
union (MkSet m1) (MkSet m2) = MkSet (Sigma.getProof $ Tree.foldr insertElement (_ ** m1) m2)
  where insertElement : (o : Ord a) => a -> Unit -> (h : Nat ** AVLTree h a o Unit) -> (h' : Nat ** AVLTree h' a o Unit)
        insertElement k v m' = runInsertRes (Tree.insert k v (Sigma.getProof m'))


||| Construct a set that contains the elements from the first input
||| set but not the second.
|||
||| *Note* Not an efficient operation as we are constructing a new set
||| instead of modifying the right one.
difference : (o : Ord a) => Set {o = o} a -> Set {o = o} a -> Set {o = o} a
difference s1 (MkSet m2) = Tree.foldr (\e,_,t => if contains e s1 then Set.insert e t else t) empty $ m2

||| Construct a set that contains common elements of the input sets.
intersection : (o : Ord a) => Set {o = o} a -> Set {o = o} a -> Set {o = o} a
intersection s1 s2 = difference s1 (difference s1 s2)

||| Construct a list using the given set.
toList : Set {o = o} a -> List a
toList (MkSet m) = map fst $ Tree.toList m

||| Construct a set from the given list.
fromList : (o : Ord a) => List a -> Set {o = o} a
fromList xs = (foldl (\t,k => Set.insert k t) empty xs)

-- --------------------------------------------------------------------- [ EOF ]
