||| A simple Queue made from two instances of `Stack`.
|||
||| An interesting exercise will be to redfine the Queue using two
||| Vectors such that properties of the Queue during a reversal can be
||| held.
module Data.Queue


data Queue : Type -> Type where
  MkQ : List a -> List a -> Queue a

mkQueue : Queue a
mkQueue = MkQ Nil Nil

pushQ : a -> Queue a -> Queue a
pushQ e (MkQ inq outq) = MkQ (e::inq) outq

initQ : a -> Queue a
initQ a = pushQ a $ mkQueue

pushQThings : List a -> Queue a -> Queue a
pushQThings xs q = foldl (flip pushQ) q xs

popQ : Queue a -> (a, Queue a)
popQ (MkQ inq (x::outq)) = (x, MkQ inq outq)
popQ (MkQ inq Nil      ) = popQ (MkQ Nil (reverse inq))

clearQ : Queue a -> Queue a
clearQ _ = mkQueue

isQEmpty : Queue a -> Bool
isQEmpty (MkQ inq outq) = isNil inq && isNil outq

-- --------------------------------------------------------------------- [ EOF ]
