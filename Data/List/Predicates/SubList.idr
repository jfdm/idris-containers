module Data.List.Predicates.SubList

import public Data.List

%default total
%access public export


||| Proof that `sub_list` is an actual sub list of `list`
data SubList : (sub_list : List ty)
            -> (list     : List ty)
            -> Type
  where
    SubNil : SubList [] xs
    InList : (prf  : Elem x ys)
          -> (rest : SubList xs ys)
          -> SubList (x :: xs) ys
