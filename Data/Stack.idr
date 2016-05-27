-- --------------------------------------------------------------- [ Stack.idr ]
-- Module    : Stack.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Helper functions to treat lists like a stack.
|||
||| A collection of aliases so that working on `List` which is used
||| like a stack, actually feels like working on a stack.
|||
||| This module is here as a convince than anything else.
module Data.Stack

-- TODO Make popS and peekS 'safe' using the magic of proofs

%access export
%default total

||| A Stack containing items of type `ty`.
|||
||| @ty The type of elements in the stack.
public export
Stack : (ty : Type) -> Type
Stack ty = List ty

||| Create an empty stack.
mkStack : Stack ty
mkStack = Nil

||| Push an element on the stack.
pushS : ty -> Stack ty -> Stack ty
pushS e Nil = [e]
pushS e xs  = e::xs

||| Initialise the stack with the given element.
initS : ty -> Stack ty
initS e = pushS e $ mkStack

||| Mass push the list of elements onto the stack.
pushSThings : List ty -> Stack ty -> Stack ty
pushSThings xs s = xs ++ s

||| Remove an element from the stack, returning the pair (head, tail).
popS : (s : Stack ty) -> {auto ok : isCons s = True} -> (ty, Stack ty)
popS Nil     {ok=Refl} impossible
popS (x::xs) {ok=p}    = (x,xs)

||| Remove an element from the stack, returning the pair (head, tail).
popS' : (s : Stack ty) -> Maybe (ty, Stack ty)
popS' Nil     = Nothing
popS' (x::xs) = Just (x,xs)

||| See what is at the top of the stack.
peekS' : (s : Stack ty) -> Maybe ty
peekS' Nil     = Nothing
peekS' (x::xs) = Just x

||| See what is at the top of the stack.
peekS : (s : Stack ty) -> {auto ok : isCons s = True} ->  ty
peekS Nil     {ok=Refl} impossible
peekS (x::xs) {ok=p}    = x

clear : Stack ty -> Stack ty
clear _ = mkStack

isSEmpty : Stack ty -> Bool
isSEmpty xs = isNil xs

-- --------------------------------------------------------------------- [ EOF ]
