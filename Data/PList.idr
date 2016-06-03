-- --------------------------------------------------------------- [ PList.idr ]
-- Module    : PList.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| A `list` construct to create lists with with values that satisfy
||| some predicate..
|||
||| The list quantifier `All` in idris is an external proof for a list
||| with type `List a`.  `PList` is a proof-carrying data structure
||| that only allows for lists to be constructed if they satisfy the
||| predicate.
module Data.PList

import public Data.DList

%access export
%default total

||| A list construct for predicated lists.
|||
||| @aTy    The type of the value contained within the list element type.
||| @elemTy The type of the elements within the list.
||| @pred   The predicate that each value must satisfy.
||| @prf    The `DList` to collect the proofs that the predicate holds.
||| @as     The List used to contain the different values within the type.
public export
data PList : (aTy    : Type)
          -> (elemTy : aTy -> Type)
          -> (pred   : aTy -> Type)
          -> (prf    : DList aTy pred ps)
          -> (as     : List aTy)
          -> Type where
  ||| Create an empty List
  Nil  : PList aTy elemTy p DList.Nil List.Nil
  ||| Cons
  |||
  ||| @elem The element to add
  ||| @rest The list for `elem` to be added to.
  ||| @prf  The proof.
  (::) : {x : aTy}
      -> (elem : elemTy x)
      -> (rest : PList aTy elemTy p prfs xs)
      -> {auto prf  : p x}
      -> PList aTy elemTy p (DList.(::) prf prfs) (List.(::) x xs)


-- -------------------------------------------------------------- [ Form Tests ]
isNil : PList aTy eTy p prfs as -> Bool
isNil Nil     = True
isNil (x::xs) = False

isCons : PList aTy eTy p prfs as -> Bool
isCons l = isNil l == False

-- ------------------------------------------------------------------ [ Length ]

length : PList aTy eTy p prfs as -> Nat
length Nil     = Z
length (x::xs) = (S Z) + length xs

-- ---------------------------------------------- [ List-Based Transformations ]

toDList : PList aTy eTy p prfs as -> DList aTy eTy as
toDList Nil     = Nil
toDList (x::xs) = DList.(::) x (toDList xs)

-- --------------------------------------------------------- [ Transformations ]
-- TODO fromLDP
-- TODO toLDP
-- TODO fromList

data PListView : (aTy : Type)
              -> {a : aTy}
              -> {pTy : aTy -> Type}
              -> {eTy : aTy -> Type}
              -> (pTy a)
              -> List (eTy a)
              -> Type
    where
      PVNil : PListView aTy p Nil
      PVOne : PListView aTy p [x]
      PVRec :  {aTy : Type}
            -> {a : aTy}
            -> {pTy : aTy -> Type}
            -> {eTy : aTy -> Type}
            -> (e : eTy a)
            -> (p : pTy a)
            -> {es : List (eTy a)}
            -> (rest : Lazy $ PListView aTy p es)
            -> PListView aTy p (e :: es)

pListView : {aTy : Type}
         -> {a : aTy}
         -> {pTy : aTy -> Type}
         -> {eTy : aTy -> Type}
         -> (p : pTy a)
         -> (es : List (eTy a))
         -> PListView aTy p es
pListView p Nil     = PVNil
pListView p [x]     = PVOne
pListView p (x::xs) = PVRec x p (pListView p xs)

fromList : (p : pTy a)
        -> List (eTy a)
        -> (as : List aTy
           ** prfs : DList aTy pTy as
           ** PList aTy eTy pTy prfs as)
fromList p xs {aTy} with (pListView {aTy} p xs)
  fromList p Nil     | PVNil = (_ ** _ ** PList.Nil)
  fromList p [x]     | PVOne = (_ ** _ ** PList.(::) {prf=p} x PList.Nil)
  fromList p (x::xs) | PVRec x p ps =
      let (as' ** prfs' ** rest) = fromList {aTy} p xs
       in (_ ** _ ** PList.(::) {prf=p} x rest)


-- ---------------------------------------------------------------- [ Indexing ]

-- TODO index
-- TODO head
-- TODO tail
-- TODO last
-- TODO Safely init the list
-- TODO Unsafely init the list.

-- --------------------------------------------------------- [ Bob The Builder ]

-- TODO append
-- TODO replicate

-- ---------------------------------------------------------------- [ SubLists ]
-- TODO take
-- TODO takeWhile
-- TODO drop
-- TODO dropWhile

-- ---------------------------------------------------------------- [ Equality ]
-- TODO eqPList

-- ------------------------------------------------------------------- [ Order ]
-- TODO cmpPList

-- ----------------------------------------------------------------- [ Folding ]
-- TODO foldr and foldl

-- ----------------------------------------------------------------- [ Functor ]
-- TODO mapPList
-- TODO map from one PList to another.
-- TODO mapMaybe
-- TODO mapMaybe from one DList to another

-- -------------------------------------------------------- [ Membership Tests ]
-- TODO make deceq tests
-- TODO any
-- TODO all
-- TODO elemBy
-- TODO elem
-- TODO hasAnyBy
-- TODO hasAny

-- --------------------------------------------------------------- [ Searching ]

-- TODO find

-- ------------------------------------------------------------- [ Conversions ]
-- TODO

-- ----------------------------------------------------------------- [ Filters ]
-- TODO

-- ------------------------------------------------------------ [ Partitioning ]
-- TODO

-- ----------------------------------------------------------------- [ Zipping ]
-- TODO

-- -------------------------------------------------------------- [ Predicates ]
-- TODO

-- ----------------------------------------------------------------- [ Sorting ]
-- TODO

-- -------------------------------------------------------------------- [ Show ]

-- TODO show
-- --------------------------------------------------------------------- [ EOF ]
