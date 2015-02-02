||| A simple two stack queue
module Data.Queue

import Data.Vect

data Queue : Type -> Type where
  MkQ : List a -> List a -> Queue a

mkQueue : Queue a
mkQueue = MkQ Nil Nil

push : a -> Queue a -> Queue a
push e (MkQ inq outq) = MkQ (e::inq) outq

initQ : a -> Queue a
initQ a = push a $ mkQueue

pushThings : List a -> Queue a -> Queue a
pushThings xs q = foldl (flip push) q xs

pop : Queue a -> (a, Queue a)
pop (MkQ inq (x::outq)) = (x, MkQ inq outq)
pop (MkQ inq Nil      ) = pop (MkQ Nil (reverse inq))

clear : Queue a -> Queue a
clear _ = mkQueue

isQEmpty : Queue a -> Bool
isQEmpty (MkQ inq outq) = isNil inq && isNil outq

-- --------------------------------------------------------------------- [ EOF ]
