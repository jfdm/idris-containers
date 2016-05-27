-- --------------------------------------------------------------- [ DVect.idr ]
-- Module    : DVect.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| A `list` construct to create lists of dependent types.
|||
||| One of the problems with using dependent types is that types
||| depend on values. This affects the ability to construct lists of
||| values that have a dependent type. The existing `List` type cannot
||| be used as it requires all elements to have the same type.
module Data.DVect

import Data.Vect

%access export

using (aTy : Type, elemTy : (aTy -> Type), x : aTy)

  ||| A list construct for dependent types.
  |||
  ||| @aTy    The type of the value contained within the list element type.
  ||| @len    The length of the list.
  ||| @elemTy The type of the elements within the list
  ||| @as     The List used to contain the different values within the type.
  public export
  data DVect : (aTy : Type)
                -> (len : Nat)
                -> (elemTy : aTy -> Type)
                -> (as : Vect len aTy)
                -> Type where
    ||| Create an empty List
    Nil  : DVect aTy Z elemTy Nil
    ||| Cons
    |||
    ||| @elem The element to add
    ||| @rest The list for `elem` to be added to.
    (::) : (elem : elemTy x)
        -> (rest : DVect aTy n elemTy xs)
        -> DVect aTy (S n) elemTy (x::xs)

-- -------------------------------------------------------------- [ Form Tests ]
isNil : DVect aTy n eTy as -> Bool
isNil Nil     = True
isNil (x::xs) = False

isCons : DVect aTy n eTy as -> Bool
isCons l = isNil l == False

-- ------------------------------------------------------------------ [ Length ]

length : DVect aTy n eTy as -> Nat
length {n} _ = n

-- ---------------------------------------------------------------- [ Indexing ]

{- TODO Safely Index the List

index : (n : Nat)
     -> (l : DVect aTy eTy as)
     -> (ok : lt n (length l) = True)
     -> (a : aTy ** eTy a)
index Z     (x::xs) p    = (_ ** x)
index (S n) (x::xs) p    = index n xs ...
index _     Nil     Refl   impossible
-}

index : (n : Nat)
     -> (l : DVect aTy l eTy as)
     -> Maybe $ DPair aTy eTy
index Z     (x::xs) = Just (_ ** x)
index (S n) (x::xs) = index n xs
index _     Nil     = Nothing

head : (l : DVect aTy n eTy as) -> {auto ok : isCons l = True} -> DPair aTy eTy
head Nil     {ok=Refl}   impossible
head (x::xs) {ok=p}    = (_ ** x)

tail : (l : DVect aTy (S n) eTy (a :: as))
    -> {auto ok : isCons l = True}
    -> (DVect aTy n eTy as)
tail Nil     {ok=Refl}   impossible
tail (x::xs) {ok=p}    = xs


last : (l : DVect aTy n eTy as) -> {auto ok : isCons l = True} -> DPair aTy eTy
last Nil        {ok=Refl}   impossible
last [x]        {ok=p}    = (_ ** x)
last (x::y::ys) {ok=p}    = last (y::ys) {ok=Refl}

-- TODO init

-- --------------------------------------------------------- [ Bob The Builder ]

(++) : DVect aTy x     eTy xs
    -> DVect aTy y     eTy ys
    -> DVect aTy (x+y) eTy (xs ++ ys)
(++) Nil     ys = ys
(++) (x::xs) ys = x :: (xs ++ ys)

-- TODO replicate

-- ---------------------------------------------------------------- [ SubLists ]
-- TODO

-- ----------------------------------------------------------------- [ Functor ]
-- TODO
{-
mapSV : (eXTy x -> eYTy y)
     -> (DVect xTy l eXTy xs)
     -> (ys : Vect l yTy ** DVect yTy l eYTy ys)
mapSV f Nil     = (Nil ** Nil)
mapSV f (x::xs) = let (ys ** xs') = mapSV f xs in (y :: ys ** f x ** xs')
-}
-- ---------------------------------------------------------------- [ Equality ]
-- TODO

-- ------------------------------------------------------------------- [ Order ]

-- TODO

-- ----------------------------------------------------------------- [ Folding ]
-- TODO

-- -------------------------------------------------------- [ Membership Tests ]
-- TODO

-- --------------------------------------------------------------- [ Searching ]
-- TODO

-- ----------------------------------------------------------------- [ Filters ]
-- TODO

-- ------------------------------------------------------------ [ Partitioning ]
-- TODO

-- -------------------------------------------------------------------- [ Show ]
-- TODO

-- ------------------------------------------- [ Applicative/Monad/Traversable ]
-- TODO

-- -------------------------------------------------------- [ Decidable Equals ]
-- TODO

-- --------------------------------------------------------------------- [ EOF ]
