module Data.List.Predicates.Thinning

import Data.List

%default total
%access public export

data Thinning : (xs,ys : List type) -> Type where
  Empty : Thinning Nil Nil
  Add   : (x : type) -> Thinning xs ys -> Thinning (x::xs) (x::ys)
  Skip  : Thinning xs ys -> Thinning xs (y::ys)

SubList : (xs,ys : List type) -> Type
SubList = Thinning
