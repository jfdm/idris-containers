-- ---------------------------------------------------------- [ Predicates.idr ]
-- Module    : Predicates.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| More Quantifiers for Lists, but keeping them out of the prelude so
||| need a new module name.
module Data.List.Predicates

import public Data.List

%default total
%access public export

||| Proof that an element is not in a list.
data NotElem : (elem : ty)
            -> (list : List ty)
            -> Type
  where
    NotHere  : NotElem x []
    NotThere : Eq ty
            => {x,y : ty}
            -> (prf : x /= y = True)
            -> NotElem x xs
            -> NotElem x (y::xs)

||| Proof that the given list is made of unique elements.
data AllDiff : (unique : List ty)
            -> Type
  where
    EmptyCase : AllDiff Nil
    OneCase   : AllDiff [x]
    ManyCase  : NotElem x xs -> AllDiff xs -> AllDiff (x::xs)

||| Proof that `sub_list` is an actual sub list of `list`
data SubList : (sub_list : List ty)
            -> (list     : List ty )
            -> Type
  where
    SubNil : SubList [] xs
    InList : (prf  : Elem x ys)
          -> (rest : SubList xs ys)
          -> SubList (x :: xs) ys


||| Proof that the contents of the given list of pairs originate from
||| a secondary list.
data PairsFromList : (pairs  : List (ty,ty))
                  -> (origin : List ty)
                  -> Type
  where
    NilPair : PairsFromList Nil as
    PairIn  : Elem a as
           -> Elem b as
           -> PairsFromList abs            as
           -> PairsFromList ((a,b) :: abs) as

||| Proof that the given list of paired elements originate from the
||| two given lists such that the following hold:
|||
|||    SubList (map fst pairs) as
|||
||| and
|||
|||    SubList (map snd pairs) bs
|||
data UnZipPairs : (pairs : List (ty,ty))
               -> (as    : List ty)
               -> (bs    : List ty)
               -> Type
  where
    UnZipOne  : UnZipPairs Nil as bs
    UnZipPair : (prf_a : Elem a as)
             -> (prf_b : Elem b bs)
             -> (rest  : UnZipPairs abs as bs)
             -> UnZipPairs ((a,b) :: abs) as bs

||| Proof that the given list of paired elements not only originate
||| from the given lists, but that all elements are unique.
data UZipPairsU : (pairs : List (ty,ty))
               -> (as    : List ty)
               -> (bs    : List ty)
               -> Type
  where
    ValidUSPU : (uniqueAs  : AllDiff as)
             -> (uniqueBs  : AllDiff bs)
             -> (uniqueABs : AllDiff (as ++ bs))
             -> (vswap     : UnZipPairs cs as bs)
             -> UZipPairsU cs as bs

-- --------------------------------------------------------------------- [ EOF ]
