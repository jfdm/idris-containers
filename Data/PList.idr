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

public export
data PList : (aTy    : Type)
          -> (elemTy : aTy -> Type)
          -> (predTy : aTy -> Type)
          -> (as     : List aTy)
          -> (prf    : DList aTy predTy as)
          -> Type
  where
    ||| Create an empty List
    Nil  : PList aTy elemTy predTy Nil Nil

    ||| Cons
    |||
    ||| @elem The element to add and proof that the element's type satisfies a certain predicate.
    ||| @rest The list for `elem` to be added to.
    (::) : (elem : elemTy x)
        -> {prf : predTy x}
        -> (rest : PList aTy elemTy predTy xs prfs)
        -> PList aTy elemTy predTy (x :: xs) (prf :: prfs)

(++) : PList aTy eTy pTy as pAs
    -> PList aTy eTy pTy bs pBs
    -> PList aTy eTy pTy (as ++ bs) (pAs ++ pBs)
(++) [] ys = ys
(++) (elem :: rest) ys = elem :: rest ++ ys

empty : PList aTy eTy pTy Nil Nil
empty = Nil

add  : (elem : elemTy x)
    -> {auto prf : predTy x}
    -> (rest : PList aTy elemTy predTy xs prfs)
    -> PList aTy elemTy predTy (x :: xs) (prf :: prfs)
add x {prf} rest = x :: rest

-- -------------------------------------------------------------- [ Form Tests ]
isNil : PList aTy eTy p as prfs -> Bool
isNil [] = True
isNil (elem :: rest) = False

isCons : PList aTy eTy p as prfs -> Bool
isCons l = isNil l == False

-- ------------------------------------------------------------------ [ Length ]

length : PList aTy eTy p as prfs -> Nat
length Nil     = Z
length (x::xs) = (S Z) + length xs

-- ---------------------------------------------- [ List-Based Transformations ]

toDList : PList aTy eTy p as prfs -> DList aTy eTy as
toDList Nil     = Nil
toDList (elem::xs) = elem :: toDList xs

toList : PList aTy eTy pTy as prfs -> List (a : aTy ** prf : pTy a ** eTy a)
toList [] = []
toList ((::) elem {x} {prf} rest) = (x ** prf ** elem) :: toList rest

fromDList : (xs   : DList aTy eTy as)
         -> (prfs : DList aTy pTy as)
         -> PList aTy eTy pTy as prfs
fromDList [] [] = []
fromDList (elem :: rest) (prf :: prfs) = elem :: fromDList rest prfs

fromList : (prf : predTy a)
        -> (xs  : List $ elemTy a)
        -> PList aTy elemTy predTy (replicate (length xs) a)
                                   (replicate (length xs) prf)
fromList prf [] = []
fromList prf (x :: xs) = x :: fromList prf xs

-- ---------------------------------------------------------------- [ Indexing ]

public export
data NonEmpty : (xs : PList aTy eTy pTy as prfs) -> Type where
  IsNonEmpty : PList.NonEmpty (x::rest)

Uninhabited (PList.NonEmpty []) where
  uninhabited IsNonEmpty impossible

nonEmpty : (xs : PList aTy eTy pTy as prfs) -> Dec (NonEmpty xs)
nonEmpty [] = No absurd
nonEmpty (elem :: rest) = Yes IsNonEmpty

public export
data InBounds : (idx : Nat)
             -> (xs : PList aTy eTy pTy as prfs)
             -> Type
  where
    InFirst : PList.InBounds Z (x::rest)
    InLater : (later : PList.InBounds idx rest)
           -> PList.InBounds (S idx) (x::rest)

Uninhabited (PList.InBounds idx []) where
  uninhabited InFirst impossible
  uninhabited (InLater _) impossible

inBounds : (idx : Nat)
        -> (xs  : PList aTy eTy pTy as prfs)
        -> Dec (InBounds idx xs)
inBounds idx Nil = No uninhabited
inBounds Z (elem :: rest) = Yes InFirst
inBounds (S k) (elem :: rest) with (inBounds k rest)
  inBounds (S k) (elem :: rest) | (Yes prf) = Yes $ InLater prf
  inBounds (S k) (elem :: rest) | (No contra) =
      No (\p => case p of
                   InLater y => contra y)

index : (idx : Nat)
     -> (xs : PList aTy eTy pTy as prfs)
     -> {auto ok   : InBounds idx xs}
     -> {auto ok'  : InBounds idx as}
     -> {auto ok'' : InBounds idx prfs}
     -> eTy (index idx as)
index Z (y :: rest) {ok = InFirst} = y
index (S k) (y :: rest) {ok = (InLater later)} {ok' = (InLater later')} {ok'' = (InLater later'')} = PList.index k rest

head : (xs : PList aTy eTy pTy (a::as) prfs)
    -> {auto ok   : NonEmpty xs}
    -> {auto ok'  : NonEmpty (a::as)}
    -> {auto ok'' : NonEmpty prfs}
    -> eTy a
head (elem :: rest) = elem

tail : (xs : PList aTy eTy pTy (a::as) (p::prfs))
    -> {auto ok   : NonEmpty xs}
    -> {auto ok'  : NonEmpty (a::as)}
    -> {auto ok'' : NonEmpty (p::prfs)}
    -> PList aTy eTy pTy as prfs
tail (elem :: rest) = rest

last : (xs : PList aTy eTy pTy as prfs)
    -> {auto ok   : NonEmpty xs}
    -> {auto ok'  : NonEmpty as}
    -> {auto ok'' : NonEmpty prfs}
    -> eTy (last as)
last [] {ok = IsNonEmpty} impossible
last (elem :: []) {ok = ok} {ok' = ok'} {ok'' = ok''} = elem
last (elem :: ((::) {prf} y rest)) {ok = ok} {ok' = ok'} {ok'' = ok''} = last $ (::) y rest {prf=prf}

init : (xs : PList aTy eTy pTy as prfs)
    -> {auto ok   : NonEmpty xs}
    -> {auto ok'  : NonEmpty as}
    -> {auto ok'' : NonEmpty prfs}
    -> PList aTy eTy pTy (init as) (init {ok=ok''} prfs)
init (y :: []) {ok = IsNonEmpty} {ok' = IsNonEmpty'} {ok'' = IsNonEmpty''} = []
init (y :: ((::) {prf} elem rest)) {ok = IsNonEmpty} {ok' = IsNonEmpty'} {ok'' = IsNonEmpty''} = y :: init (elem :: rest)



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
