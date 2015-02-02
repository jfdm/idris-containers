||| Implementation of a Set using an AVL Binary Search Tree.
|||
||| Code adapted from Haskell sources from `Data.FiniteMap` and `Data.Map`.
|||
||| For theory see:
|||
||| * Stephen Adams, 'Efficient sets: a balancing act', Journal of
||| Functional Programming 3(4):553-562, October 1993,
||| http://www.swiss.ai.mit.edu/~adams/BB/.
||| * J. Nievergelt and E.M. Reingold, 'Binary search trees of bounded
||| balance', SIAM journal of computing 2(1), March 1973.
module Data.AVL.Set

import Data.AVL.Tree

data Set a = MkSet (AVLTree a)

||| Return a empty set.
empty : Set a
empty = MkSet Empty

||| Insert an element into a set.
insert : Ord a => a -> Set a -> Set a
insert a (MkSet m) = MkSet (avlInsert a m)

||| Remove an element from the set.
delete : Ord a => a -> Set a -> Set a
delete a (MkSet m) = MkSet (avlRemove a m)

||| Does the set contain the given element.
contains : Ord a => a -> Set a -> Bool
contains a (MkSet m) = isJust (avlLookup a m)


||| Construct a list using the given set.
toList : Set a -> List a
toList (MkSet m) = avlToList m

||| Construct a set from the given list.
fromList : Ord a => List a -> Set a
fromList xs = MkSet ((foldl (flip avlInsert) Empty xs))


instance Functor Set where
  map f (MkSet Empty) = MkSet Empty
  map f (MkSet t)     = MkSet $ map f t

instance Foldable Set where
  foldr f e xs = foldr f e (Set.toList xs)

-- --------------------------------------------------------------------- [ EOF ]
