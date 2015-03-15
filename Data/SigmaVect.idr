||| A `list` construct to create lists of dependent types.
|||
||| One of the problems with using dependent types is that types
||| depend on values. This affects the ability to construct lists of
||| values that have a dependent type. The existing `List` type cannot
||| be used as it requires all elements to have the same type.
module Data.SigmaList

import Data.Vect

using (aTy : Type, elemTy : (aTy -> Type), x : aTy)

  ||| A list construct for dependent types.
  |||
  ||| @aTy    The type of the value contained within the list element type.
  ||| @len    The length of the list.
  ||| @elemTy The type of the elements within the list
  ||| @as     The List used to contain the different values within the type.
  data SigmaList : (aTy : Type)
                -> (len : Nat)
                -> (elemTy : aTy -> Type)
                -> (as : Vect len aTy)
                -> Type where
    ||| Create an empty List
    Nil  : SigmaList aTy Z elemTy Nil
    ||| Cons
    |||
    ||| @elem The element to add
    ||| @rest The list for `elem` to be added to.
    (::) : (elem : elemTy x)
        -> (rest : SigmaList aTy n elemTy xs)
        -> SigmaList aTy (S n) elemTy (x::xs)

||| Alisasing before syntactic sugar can be defined and added.
SList : (aTy : Type) -> (n : Nat) -> (elemTy : aTy -> Type) -> Vect n aTy -> Type
SList = SigmaList

-- -------------------------------------------------------------- [ Form Tests ]
isNil : SigmaList aTy n eTy as -> Bool
isNil Nil     = True
isNil (x::xs) = False

isCons : SigmaList aTy n eTy as -> Bool
isCons l = isNil l == False

-- ------------------------------------------------------------------ [ Length ]

length : SigmaList aTy n eTy as -> Nat
length {n} _ = n

-- ---------------------------------------------------------------- [ Indexing ]

{- TODO Safely Index the List

index : (n : Nat)
     -> (l : SigmaList aTy eTy as)
     -> (ok : lt n (length l) = True)
     -> (a : aTy ** eTy a)
index Z     (x::xs) p    = (_ ** x)
index (S n) (x::xs) p    = index n xs ...
index _     Nil     Refl   impossible
-}

index : (n : Nat)
     -> (l : SigmaList aTy l eTy as)
     -> Maybe $ Sigma aTy eTy
index Z     (x::xs) = Just (_ ** x)
index (S n) (x::xs) = index n xs
index _     Nil     = Nothing

head : (l : SigmaList aTy n eTy as) -> {auto ok : isCons l = True} -> Sigma aTy eTy
head Nil     {ok=Refl}   impossible
head (x::xs) {ok=p}    = (_ ** x)

tail : (l : SigmaList aTy (S n) eTy (a :: as))
    -> {auto ok : isCons l = True}
    -> (SigmaList aTy n eTy as)
tail Nil     {ok=Refl}   impossible
tail (x::xs) {ok=p}    = xs


last : (l : SigmaList aTy n eTy as) -> {auto ok : isCons l = True} -> Sigma aTy eTy
last Nil        {ok=Refl}   impossible
last [x]        {ok=p}    = (_ ** x)
last (x::y::ys) {ok=p}    = last (y::ys) {ok=Refl}

-- TODO init

-- --------------------------------------------------------- [ Bob The Builder ]

(++) : SigmaList aTy x     eTy xs
    -> SigmaList aTy y     eTy ys
    -> SigmaList aTy (x+y) eTy (xs ++ ys)
(++) Nil     ys = ys
(++) (x::xs) ys = x :: (xs ++ ys)

-- TODO replicate

-- ---------------------------------------------------------------- [ SubLists ]
-- TODO

-- ----------------------------------------------------------------- [ Functor ]
-- TODO


mapSV' : (eXTy x -> eYTy y)
     -> (SigmaList xTy Z eXTy Nil)
     -> (SigmaList yTy Z eYTy Nil)
mapSV' f Nil = Nil

mapSV : (eXTy x -> eYTy y)
     -> (SigmaList xTy l eXTy xs)
     -> (ys : Vect l yTy ** SigmaList yTy l eYTy ys)
mapSV f Nil     = (Nil ** Nil)
mapSV f (x::xs) = let (ys ** xs') = mapSV f xs in (y :: ys ** f x ** xs')

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
