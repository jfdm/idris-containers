module Data.List.Predicates.Unique.Old

import Data.List

%access public export
%default total

||| Proof that a list `xs` is unique.
data Unique : (xs : List type) -> Type where

  ||| Empty lists are 'unique'
  Empty : Unique Nil

  ||| Only add an element to the list is it doesn't appear in the
  ||| remaining lists.
  Cons : (x : type)
      -> (prfU : Not (Elem x xs))
      -> (rest : Unique xs)
      -> Unique (x::xs)

-- ----------------------------------------------------------------- [ Helpers ]
duplicateElement : (prf : Elem x xs) -> Unique (x :: xs) -> Void
duplicateElement prf (Cons x f rest) = f prf

restNotUnique : (f : Unique xs -> Void) -> (contra : Elem x xs -> Void) -> Unique (x :: xs) -> Void
restNotUnique f contra (Cons x g rest) = f rest

||| Is the list `xs` unique?
unique : DecEq type
      => (xs : List type)
      -> Dec (Unique xs)
unique [] = Yes Empty
unique (x :: xs) with (isElem x xs)
  unique (x :: xs) | (Yes prf) = No (duplicateElement prf)
  unique (x :: xs) | (No contra) with (unique xs)
    unique (x :: xs) | (No contra) | (Yes prf) = Yes (Cons x contra prf)
    unique (x :: xs) | (No contra) | (No f) = No (restNotUnique f contra)

-- --------------------------------------------------------------------- [ EOF ]
