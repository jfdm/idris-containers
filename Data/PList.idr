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

||| A list construct for predicated lists.
|||
||| @elemTy The type of the elements within the list
||| @pred   The predicate that each value must satisfy.
||| @prf     The `DList` to collect the proofs that the predicate holds.
public export
data PList : (elemTy : Type)
          -> (pred   : elemTy -> Type)
          -> (prf    : DList elemTy pred ps)
          -> Type where
  ||| Create an empty List
  Nil  : PList ty p DList.Nil
  ||| Cons
  |||
  ||| @elem The element to add
  ||| @rest The list for `elem` to be added to.
  (::) : (elem : ty)
      -> (rest : PList ty p ps)
      -> {prf : p elem}
      -> PList ty p (DList.(::) prf ps)

-- -------------------------------------------------------------- [ Form Tests ]
isNil : PList eTy p prfs -> Bool
isNil Nil     = True
isNil (x::xs) = False

isCons : PList eTy p prfs -> Bool
isCons l = isNil l == False

-- ------------------------------------------------------------------ [ Length ]

length : PList eTy p prfs -> Nat
length Nil     = Z
length (x::xs) = (S Z) + length xs

-- ---------------------------------------------------------------- [ Indexing ]

-- TODO Safely Index the List

index : (n : Nat)
     -> (l : PList eTy p prfs)
     -> Maybe $ eTy
index Z     (x::xs) = Just x
index (S n) (x::xs) = index n xs
index _     Nil     = Nothing

head : (l : PList eTy p prfs)
    -> {auto ok : isCons l = True}
    -> eTy
head Nil     {ok=Refl}   impossible
head (x::xs) {ok=p}    = x

tail : (l : PList eTy p (prf :: prfs))
    -> {auto ok : isCons l = True}
    -> (PList eTy p prfs)
tail Nil     {ok=Refl}   impossible
tail (x::xs) {ok=p}    = xs

{-}
last : (l : PList eTy p prfs)
    -> {auto ok : isCons l = True}
    -> eTy
last Nil     {ok=Refl} impossible
last (x::xs) {ok=a}    with (xs)
  | Nil     = x
  | [y]     = y
  | (y::ys) = last ys {ok=Refl}

-}
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

-- --------------------------------------------------------- [ Transformations ]
-- TODO fromLDP

-- ---------------------------------------------- [ To List of Dependent Pairs ]

-- TODO toLDP

-- ----------------------------------------------------------- [ List to DList ]
-- TODO fromList

-- -------------------------------------------------------- [ Membership Tests ]
-- TODO make deceq tests
{-
any : ({a : aTy} -> elemTy a -> Bool)
   -> DList aTy elemTy as
   -> Bool
any p = DList.foldr (\e,res => res || p e) False

all : ({a : aTy} -> elemTy a -> Bool)
   -> DList aTy elemTy as
   -> Bool
all p = DList.foldr (\e,res => res && p e) True

elemBy : ({a,b : aTy} -> elemTy a -> elemTy b -> Bool)
      -> elemTy a
      -> DList aTy elemTy as
      -> Bool
elemBy p e = any (\x => p e x)
-}

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
