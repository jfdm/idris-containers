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

import Data.AVL.Dict

data Set a = MkSet (Dict a Unit)

||| Return a empty set.
empty : Set a
empty = MkSet Empty

||| Insert an element into a set.
insert : Ord a => a -> Set a -> Set a
insert a (MkSet m) = MkSet (insert a () m)

||| Remove an element from the set.
delete : Ord a => a -> Set a -> Set a
delete a (MkSet m) = MkSet (remove a m)

||| Does the set contain the given element.
contains : Ord a => a -> Set a -> Bool
contains a (MkSet m) = isJust (lookup a m)

||| Construct a set that contains all elements in both of the input sets.
union : Ord a => Set a -> Set a -> Set a
union (MkSet m1) (MkSet m2) = MkSet (merge m1 m2)

||| Construct a set that contains the elements from the first input set but not the second.
difference : Ord a => Set a -> Set a -> Set a
difference (MkSet m1) (MkSet m2) = MkSet (foldl (\ t, (k, ()) => remove k t) empty (with Dict toList m2))

||| Construct a set that contains common elements of the input sets.
intersection : Ord a => Set a -> Set a -> Set a
intersection s1 s2 = difference s1 (difference s1 s2)

||| Construct a list using the given set.
toList : Set a -> List a
toList (MkSet m) = map fst $ toList m

||| Construct a set from the given list.
fromList : Ord a => List a -> Set a
fromList xs = MkSet ((foldl (\t,k => insert k () t) Empty xs))

instance Foldable Set where
  foldr f e xs = foldr f e (Set.toList xs)

-- --------------------------------------------------------------------- [ EOF ]
