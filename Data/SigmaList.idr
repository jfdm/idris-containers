||| A `list` construct to create lists of dependent types.
|||
||| One of the problems with using dependent types is that types
||| depend on values. This affects the ability to construct lists of
||| values that have a dependent type. The existing `List` type cannot
||| be used as it requires all elements to have the same type.
module Data.SigmaList


using (aTy : Type, elemTy : (aTy -> Type), x : aTy)

  ||| A list construct for dependent types.
  |||
  ||| @aTy    The type of the value contained within the list element type.
  ||| @elemTy The type of the elements within the list
  ||| @as     The List used to contain the different values within the type.
  data SigmaList : (aTy : Type)
                -> (elemTy : aTy -> Type)
                -> (as : List aTy)
                -> Type where
    ||| Create an empty List
    Nil  : SigmaList aTy elemTy Nil
    ||| Cons
    |||
    ||| @elem The element to add
    ||| @rest The list for `elem` to be added to.
    (::) : (elem : elemTy x)
        -> (rest : SigmaList aTy elemTy xs)
        -> SigmaList aTy elemTy (x::xs)

||| Alisasing before syntactic sugar can be defined and added.
SList : (aTy : Type) -> (elemTy : aTy -> Type) -> List aTy -> Type
SList = SigmaList

-- -------------------------------------------------------------- [ Form Tests ]
isNil : SigmaList aTy eTy as -> Bool
isNil Nil     = True
isNil (x::xs) = False

isCons : SigmaList aTy eTy as -> Bool
isCons l = isNil l == False

-- ------------------------------------------------------------------ [ Length ]

length : SigmaList aTy eTy as -> Nat
length Nil     = Z
length (x::xs) = (S Z) + length xs

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
     -> (l : SigmaList aTy eTy as)
     -> Maybe $ Sigma aTy eTy
index Z     (x::xs) = Just (_ ** x)
index (S n) (x::xs) = index n xs
index _     Nil     = Nothing

head : (l : SigmaList aTy eTy as) -> {auto ok : isCons l = True} -> Sigma aTy eTy
head Nil     {ok=Refl}   impossible
head (x::xs) {ok=p}    = (_ ** x)

tail : (l : SigmaList aTy eTy (a :: as))
    -> {auto ok : isCons l = True}
    -> (SigmaList aTy eTy as)
tail Nil     {ok=Refl}   impossible
tail (x::xs) {ok=p}    = xs


last : (l : SigmaList aTy eTy as) -> {auto ok : isCons l = True} -> Sigma aTy eTy
last Nil        {ok=Refl}   impossible
last [x]        {ok=p}    = (_ ** x)
last (x::y::ys) {ok=p}    = last (y::ys) {ok=Refl}

-- TODO init

-- --------------------------------------------------------- [ Bob The Builder ]

(++) : SigmaList aTy eTy xs -> SigmaList aTy eTy ys -> SigmaList aTy eTy (xs ++ ys)
(++) Nil     ys = ys
(++) (x::xs) ys = x :: (xs ++ ys)

-- TODO replicate

-- ---------------------------------------------------------------- [ SubLists ]
-- TODO

-- ----------------------------------------------------------------- [ Functor ]
-- TODO

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

showElem : ((aTy -> Type) -> String) -> (aTy -> Type) -> String
showElem showE e = showE e

using (aTy : Type, eTy : aTy -> Type, xs : List aTy)

  showSList : SigmaList aTy eTy xs -> List String
  showSList Nil     = [""]
  showSList (x::xs) = showElem show x :: showSList xs

  instance (ShowSigmaList aTy eTy ys) => Show (SigmaList aTy eTy ys) where
     show xs = unwords ["[", concat (intersperse "," (showSList xs)), "]"]

-- ------------------------------------------- [ Applicative/Monad/Traversable ]
-- TODO

-- -------------------------------------------------------- [ Decidable Equals ]
-- TODO

-- --------------------------------------------------------------------- [ EOF ]
