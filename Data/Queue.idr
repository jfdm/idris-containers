-- --------------------------------------------------------------- [ Queue.idr ]
-- Module    : Queue.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| A simple Queue made from two instances of `Stack`.
|||
||| An interesting exercise will be to redfine the Queue using two
||| Vectors such that properties of the Queue during a reversal can be
||| held.
module Data.Queue

-- TODO Make popQ and peekQ 'safe' using the magic of proofs
-- TODO Make popQ total

%access export
%default total

||| A Queue of items of type `ty`.
|||
||| @ty The type of elements in the queue.
data Queue : (ty : Type) -> Type where
  MkQ : List a -> List a -> Queue a

||| Create an empty queue
mkQueue : Queue ty
mkQueue = MkQ Nil Nil

||| Is the Queue empty.
isQEmpty : Queue a -> Bool
isQEmpty (MkQ inq outq) = isNil inq && isNil outq

||| Is the queue cons
isQCons : Queue a -> Bool
isQCons (MkQ inq outq) = isCons inq || isCons outq

||| Push an element onto the queue.
pushQ : a -> Queue a -> Queue a
pushQ e (MkQ inq outq) = MkQ (e::inq) outq

||| Initialise the queue with the given element.
initQ : ty -> Queue ty
initQ e = pushQ e $ mkQueue

||| Mass push a list of things onto the queue.
pushQThings : List a -> Queue a -> Queue a
pushQThings xs q = foldl (flip pushQ) q xs

||| Remove an element from the queue, returning the pair (head, tail)
||| @q The Q
partial
popQ : (q : Queue ty) -> {auto prf : isQCons q = True} ->  (ty, Queue ty)
popQ (MkQ Nil Nil) {prf=Refl} impossible
popQ (MkQ Nil [x])            = (x, MkQ Nil Nil)
popQ (MkQ (x :: xs) (y :: (z :: ys))) = (y, MkQ (x::xs) ys)
popQ (MkQ (x :: xs) Nil) = case (reverse (x::xs)) of
  (y::ys) => (y, MkQ Nil ys)
popQ (MkQ (x :: xs) [y]) = (y, MkQ Nil (reverse (x::xs)))
popQ (MkQ Nil (x :: (y :: xs))) = (x, MkQ Nil (y::xs))



||| See what is at the top of the Queue
|||
||| @q the Q
partial
peekQ : (q : Queue ty) -> {auto prf : isQCons q = True} -> ty
peekQ qu = fst $ popQ qu

||| Remove an element from the queue, returning the pair (head, tail)
||| @q The Q
partial
popQ' : (q : Queue ty) -> Maybe (ty, Queue ty)
popQ' (MkQ Nil Nil)  = Nothing
popQ' (MkQ inq xs)   with (xs)
  | Nil       = popQ' (MkQ Nil (reverse inq))
  | (x::outq) = Just (x, MkQ inq outq)

||| See what is at the top of the Queue
|||
||| @q the Q
peekQ' : (q : Queue ty) -> Maybe ty
peekQ' (MkQ Nil Nil)       = Nothing
peekQ' (MkQ inq (x::outq)) = Just x
peekQ' (MkQ inq Nil)       = head' (reverse inq)

clearQ : Queue a -> Queue a
clearQ _ = mkQueue

implementation Eq ty => Eq (Queue ty) where
  (==) (MkQ inx outx) (MkQ iny outy) = inx == iny && outx == outy

implementation Show ty => Show (Queue ty) where
  show (MkQ inq outq) = unwords ["[Q", show inq, show outq, "]"]
-- --------------------------------------------------------------------- [ EOF ]
