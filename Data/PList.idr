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

import public Data.List
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

Sized (PList aTy eTy pTy as prfs) where
  size = length

eqPList : ({a,b : aTy} -> elemTy a -> elemTy b -> Bool)
       -> PList aTy elemTy predTy as aPrfs
       -> PList aTy elemTy predTy bs bPrfs
       -> Bool
eqPList _ Nil     Nil     = True
eqPList p (x::xs) (y::ys) =
  if p x y
    then eqPList p xs ys
    else False
eqPList _ _       _       = False


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
init (y :: []) {ok = IsNonEmpty} {ok' = IsNonEmpty} {ok'' = IsNonEmpty} = []
init (y :: ((::) {prf} elem rest)) {ok = IsNonEmpty} {ok' = IsNonEmpty} {ok'' = IsNonEmpty} = y :: init (elem :: rest)

public export
data Elem : (aTy    : Type)
         -> (elemTy : aTy -> Type)
         -> (predTy : aTy -> Type)
         -> (a : aTy)
         -> (x : elemTy a)
         -> (prf : predTy a)
         -> (xs   : PList aTy elemTy predTy as prfs)
         -> (prfA : Elem a as)
         -> (prfP : DElem aTy predTy prf prfs prfA)
         -> Type
  where
    Hier  : PList.Elem aTy eTy pTy a x p (x::xs) Here (Hier Refl)
    Er    : (rest : PList.Elem aTy eTy pTy a x p xs prfA prfP)
         -> PList.Elem aTy eTy pTy a x p (x'::xs) (There prfA) (DList.Er prfP)

Uninhabited (PList.Elem aTy eTy pTy a x prf Nil prfA prfP) where
  uninhabited Hier impossible
  uninhabited (Er _) impossible

dropElem : (as   : PList iTy elemTy predTy is prfs)
        -> (idxP : Elem iTy elemTy predTy i e prf as prfA prfP)
        -> PList iTy elemTy predTy (dropElem is prfA) (dropElem prfs prfP)
dropElem (e :: x) Hier = x
dropElem (x :: z) (Er rest) = x :: dropElem z rest

delete' : (x  : elemTy i)
       -> (xs : PList iTy elemTy predTy is prfs)
       -> (idxVal : Elem i is)
       -> (idxPrf : DElem iTy predTy prf prfs idxVal)
       -> PList iTy elemTy predTy (dropElem is idxVal) (dropElem prfs idxPrf)
delete' x (elem :: rest) Here (Hier Refl) = rest
delete' x (elem :: rest) (There later) (Er komst) = elem :: delete' x rest later komst

delete : (x  : elemTy i)
      -> (xs : PList iTy elemTy predTy is prfs)
      -> {auto idxVal : Elem i is}
      -> {auto idxPrf : DElem iTy predTy prf prfs idxVal}
      -> PList iTy elemTy predTy (dropElem is idxVal) (dropElem prfs idxPrf)
delete x xs {idxVal} {idxPrf} = delete' x xs idxVal idxPrf


-- --------------------------------------------------------- [ Bob The Builder ]

-- TODO append
-- TODO replicate

-- ---------------------------------------------------------------- [ SubLists ]

take : (n : Nat)
    -> (xs : PList aTy elemTy predTy as prfs)
    -> PList aTy elemTy predTy (take n as) (take n prfs)
take Z     xs             = Nil
take (S k) []             = Nil
take (S k) (elem :: rest) = elem :: take k rest

-- TODO takeWhile

-- TODO drop
drop : (n : Nat)
    -> (xs : PList aTy elemTy predTy as prfs)
    -> PList aTy elemTy predTy (drop n as) (drop n prfs)
drop Z     rest           = rest
drop (S k) []             = Nil
drop (S k) (elem :: rest) = drop k rest

-- TODO dropWhile

-- ---------------------------------------------------------------- [ Equality ]
-- TODO eqPList

-- ------------------------------------------------------------------- [ Order ]
-- TODO cmpPList

-- ----------------------------------------------------------------- [ Folding ]
-- TODO foldr and foldl
foldr : ({a : aTy} -> elemTy a -> p -> p)
     -> p
     -> PList aTy elemTy predTy as prfs
     -> p
foldr f init Nil     = init
foldr f init (x::xs) = f x (PList.foldr f init xs)

foldl : ({a : aTy} -> p -> elemTy a -> p)
      -> p
      -> PList aTy elemTy predTy as prfs
      -> p
foldl f init Nil = init
foldl f init (x::xs) = PList.foldl f (f init x) xs

-- ----------------------------------------------------------------- [ Functor ]

map : ({a : aTy} -> elemTy a -> b)
   -> PList aTy elemTy predTy as prf
   -> List b
map f Nil     = List.Nil
map f (x::xs) = with List f x :: map f xs


mapMaybe : ({a : aTy} -> elemTy a -> Maybe b)
         -> PList aTy elemTy predTy as prfs
         -> List b
mapMaybe f Nil     = Nil
mapMaybe f (x::xs) =
  case f x of
    Nothing => mapMaybe f xs
    Just y  => y :: mapMaybe f xs

concatMap : Monoid m
         => (func : {a : aTy} -> elemTy a -> m)
         -> (xs : PList aTy elemTy predTy as prfs)
         -> m
concatMap f = foldr (\e, res => f e <+> res) neutral


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

private
doPListShow : ({a : aTy} -> elemTy a -> String)
           -> PList aTy elemTy predTy as prfs
           -> List String
doPListShow _  Nil     = Nil
doPListShow f  (x::xs) = (f x) :: doPListShow f xs

showPList : (showFunc : {a : aTy} -> elemTy a -> String)
         -> (l : PList aTy elemTy predTy as prfs)
         -> String
showPList f xs = "[" ++ unwords (intersperse "," (doPListShow f xs)) ++ "]"

-- --------------------------------------------------------------------- [ EOF ]
