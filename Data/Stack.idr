||| A collection of aliases so that working on `List` which is used
||| like a stack, actually feels like working on a stack.
|||
||| This module is here as a convince than anything else.
module Data.Stack

Stack : Type -> Type
Stack a = List a

mkStack : Stack a
mkStack = Nil

pushS : a -> Stack a -> Stack a
pushS e Nil = [e]
pushS e xs  = e::xs

initS : a -> Stack a
initS a = pushS a $ mkStack

pushSThings : List a -> Stack a -> Stack a
pushSThings xs s = xs ++ s

popS : Stack a -> (a, Stack a)
popS (x::xs) = (x,xs)

clear : Stack a -> Stack a
clear _ = mkStack

isSEmpty : Stack a -> Bool
isSEmpty xs = isNil xs

-- --------------------------------------------------------------------- [ EOF ]
