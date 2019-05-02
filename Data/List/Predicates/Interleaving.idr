module Data.List.Predicates.Interleaving

import Data.List

%access public export
%default total

data Interleaving : (xs, ys, zs : List type) -> Type where
  Empty   : Interleaving Nil Nil Nil
  LeftAdd : (x : type)
         -> (rest : Interleaving xs ys zs)
         -> Interleaving (x::xs) ys (x::zs)
  RightAdd : (y : type)
          -> (rest : Interleaving xs ys zs)
          -> Interleaving xs (y::ys) (y::zs)

leftEmpty : (ys : List type) -> Interleaving Nil ys ys
leftEmpty [] = Empty
leftEmpty (x :: xs) = RightAdd x (leftEmpty xs)

leftEmptyCons : (x : type) -> (xs : List type) -> Interleaving Nil (x::xs) (x::xs)
leftEmptyCons x [] = RightAdd x Empty
leftEmptyCons x (y :: xs) with (leftEmptyCons y xs)
  leftEmptyCons x (y :: xs) | (RightAdd y rest) = RightAdd x (RightAdd y rest)

rightEmpty : (xs : List type) -> Interleaving xs Nil xs
rightEmpty [] = Empty
rightEmpty (x :: xs) = LeftAdd x (rightEmpty xs)
