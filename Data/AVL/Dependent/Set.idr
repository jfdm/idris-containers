||| Implementation of a Set using an AVL Binary Search Tree.
module Data.AVL.Dependent.Set

import Data.AVL.Dependent.Dict

-- ||| Alias for make it easier to work with.
-- Set : Nat -> (k : Type) -> {default %instance o : Ord k} -> Type
-- Set n k {o = o} = Dict' n k o Unit

data Set : Type -> Type where
  MkSet : {a : Type} -> {default %instance o : Ord a} -> Dict' n a o Unit -> Set a

||| Return a empty set.
empty : Ord a => Set a
empty = MkSet Empty

||| Insert an element into a set.
insert : Ord a => a -> Set a -> Set a
insert a (MkSet m) = case (Dict.insert a () m) of
  Grew x => MkSet x
  Same x => MkSet x

||| Does the set contain the given element.
contains : Ord a => a -> Set a -> Bool
contains a (MkSet m) = isJust (lookup a m)

||| Construct a set that contains all elements in both of the input sets.
union : Ord a => Set a -> Set a -> Set a
union (MkSet m1) (MkSet m2) = MkSet $ Sigma.getProof $ fromList $ toList m1 ++ toList m2


-- ||| Remove an element from the set.
-- delete : Ord a => a -> Set a -> Set a
-- delete a (MkSet m) = MkSet (remove a m)

-- ||| Construct a set that contains the elements from the first input set but not the second.
-- difference : Ord a => Set a -> Set a -> Set a
-- difference (MkSet m1) (MkSet m2) = MkSet (foldl (\ t, (k) => remove k t) empty (Tree.toList m2))

-- ||| Construct a set that contains common elements of the input sets.
-- intersection : Ord a => Set a -> Set a -> Set a
-- intersection s1 s2 = difference s1 (difference s1 s2)

||| Construct a list using the given set.
toList : Set a -> List a
toList (MkSet m) = map fst $ Dict.toList m

||| Construct a set from the given list.
fromList : Ord a => List a -> Set a
fromList xs = (foldl (\t,k => Set.insert k t) empty xs)

instance Foldable Set where
  foldr f e xs = foldr f e (Set.toList xs)

-- --------------------------------------------------------------------- [ EOF ]
