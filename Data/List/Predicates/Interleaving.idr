module Data.List.Predicates.Interleaving

import Data.List

%access public export
%default total

data Interleaving : (xs, ys, zs : List a) -> Type where
  Empty   : Interleaving Nil Nil Nil
  LeftAdd : (x : type)
         -> Interleaving xs ys zs
         -> Interleaving (x::xs) ys (x::zs)
  RightAdd : (y : type)
          -> Interleaving xs ys zs
          -> Interleaving xs (y::ys) (y::zs)
