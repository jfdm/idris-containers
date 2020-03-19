module Data.List.Predicates.Pairs.Old

import public Data.List

import public Data.List.Predicates.Interleaving
import public Data.List.Predicates.Unique.Old

%default total
%access public export

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
    ValidUSPU : (uniqueAs  : Unique as)
             -> (uniqueBs  : Unique bs)
             -> (uniqueABs : Unique (as ++ bs))
             -> (vswap     : UnZipPairs cs as bs)
             -> UZipPairsU cs as bs
