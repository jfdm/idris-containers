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

import Data.DList

import public Decidable.Equality.Indexed

%default total
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
            -> (elemTy : aTy -> Type)
            -> (len : Nat)
            -> (as : Vect len aTy)
            -> Type where
    ||| Create an empty List
    Nil  : DVect aTy elemTy Z Nil
    ||| Cons
    |||
    ||| @ex The element to add
    ||| @rest The list for `elem` to be added to.
    (::) : (ex : elemTy x)
        -> (rest : DVect aTy elemTy n xs)
        -> DVect aTy elemTy (S n) (x::xs)


(++) : DVect aTy eTy x     xs
    -> DVect aTy eTy y     ys
    -> DVect aTy eTy (x+y) (xs ++ ys)
(++) Nil     ys = ys
(++) (x::xs) ys = x :: (xs ++ ys)

-- -------------------------------------------------------------- [ Form Tests ]
isNil : DVect aTy elemTy n as -> Bool
isNil Nil     = True
isNil (x::xs) = False

isCons : DVect aTy elemTy n as -> Bool
isCons l = isNil l == False

-- ------------------------------------------------------------------ [ Length ]

length : DVect aTy elemTy n as -> Nat
length {n} _ = n

-- ---------------------------------------------------------------- [ Indexing ]

index : (idx : Fin l)
     -> (vs : DVect aTy elemTy l as)
     -> elemTy (index idx as)
index FZ (ex :: rest) = ex
index (FS x) (ex :: rest) = index x rest

head : (vs : DVect aTy elemTy (S n) (a::as))
    -> elemTy a
head (ex :: rest) = ex


tail : (vs : DVect aTy eTy (S n) (a :: as))
    -> (DVect aTy eTy n as)
tail (ex :: rest) = rest

last : (vs : DVect aTy eTy (S n) as)
    -> eTy (last as)
last (ex :: rest) with (rest)
  last (ex :: rest) | [] = ex
  last (ex :: rest) | (ey :: xs) = last (ey::xs)

init : (vs : DVect aTy eTy (S n) as)
    -> DVect aTy eTy n (init as)
init (ex :: []) = []
init (ex :: (ey :: zs)) = ex :: init (ey::zs)

-- TODO insertAt
-- TODO deleteAt
-- TODO relaceAt
-- TODO updateAt

take : (n : Nat)
    -> (vs : DVect aTy eTy (n+m) as)
    -> DVect aTy eTy n (take n as)
take Z vs = []
take (S k) (ex :: rest) = ex :: take k rest



takeWhile' : ({i : aTy} -> eTy i -> Bool)
          -> (vs : DVect aTy eTy l is)
          -> (l' : Nat ** bs : Vect l' aTy ** DVect aTy eTy l' bs)
takeWhile' f Nil = (_ ** _ ** Nil)
takeWhile' f (ex :: rest) =
  if f ex
  then (_ ** _ ** DVect.(::) ex (snd $ snd (takeWhile' f rest)))
  else (_ ** _ ** Nil)

drop : (n  : Nat)
    -> (vs : DVect aTy eTy (n + m) as)
    -> DVect aTy eTy m (drop n as)
drop Z vs = vs
drop (S k) (ex :: rest) = drop k rest

dropWhile' : ({i : aTy} -> eTy i -> Bool)
          -> (vs : DVect aTy eTy l is)
          -> (l' : Nat ** bs : Vect l' aTy ** DVect aTy eTy l' bs)
dropWhile' f Nil = (_ ** _ ** Nil)
dropWhile' f (ex :: rest) =
  if f ex
  then dropWhile' f rest
  else (_ ** _ ** DVect.(::) ex rest)


replicate : (n : Nat)
         -> (e : eTy i)
         -> DVect aTy eTy n (replicate n i)
replicate Z e = []
replicate (S k) e = e :: replicate k e

equals : ({i,j : aTy} -> e i -> e j -> Bool)
       -> DVect aTy e a as
       -> DVect aTy e b bs
       -> Bool
equals _ Nil Nil = True
equals f (x::xs) (y::ys) =
  if f x y
  then equals f xs ys
  else False
equals _ _ _ = False

compare : ({i,j : aTy} -> e i -> e j -> Bool)
        -> ({i,j : aTy} -> e i -> e j -> Ordering)
        -> DVect aTy e a as
        -> DVect aTy e b bs
        -> Ordering
compare _ _ Nil Nil = EQ
compare _ _ Nil _   = LT
compare _ _ _   Nil = GT
compare e c (a::as) (b::bs) =
  if (not (e a b))
  then c a b
  else compare e c as bs

concat : (xss : DVect (Vect n iTy) (DVect iTy e n) m iis)
      -> DVect iTy e (m * n) (concat iis)
concat [] = Nil
concat (ex :: rest) = ex ++ concat rest

foldr : ({i : iTy} -> e i -> p -> p)
     -> p
     -> DVect iTy e l as
     -> p
foldr _ acc Nil = acc
foldr f acc (x::xs) = f x (foldr f acc xs)

foldl : ({i : iTy} -> p -> e i -> p)
     -> p
     -> DVect iTy e l as
     -> p
foldl f init Nil = init
foldl f init (x::xs) = foldl f (f init x) xs

mapToVect : ({i : iTy} -> e i -> b)
         -> DVect iTy e l as
         -> Vect l b
mapToVect _ Nil = Nil
mapToVect f (x::xs) = f x :: mapToVect f xs

mapToList : ({i : iTy} -> e i -> b)
         -> DVect iTy e l as
         -> List b
mapToList f Nil = Nil
mapToList f (ex :: rest) = f ex :: mapToList f rest

toList' : Vect l type -> List type
toList' [] = []
toList' (x :: xs) = x :: toList' xs

mapToDList : DVect iTy e l as
          -> DList iTy e (toList' as)
mapToDList [] = []
mapToDList (ex :: rest) = ex :: mapToDList rest


mapMaybeToVect : ({i : iTy} -> e i -> Maybe b)
              -> DVect iTy e l as
              -> (l' ** Vect l' b)
mapMaybeToVect f Nil = (_ ** Nil)
mapMaybeToVect f (x::xs) =
  let rest = mapMaybeToVect f xs in
   case f x of
     Nothing => rest
     Just y  => (_ ** y :: (snd rest))

zipWith : (fT : iTy -> jTy -> kTy)
       -> (fV : {i : iTy} -> {j : jTy} -> e i -> f j -> g (fT i j))
       -> (xs : DVect iTy e l as)
       -> (ys : DVect jTy f l bs)
       -> DVect kTy g l (zipWith fT as bs)
zipWith fT fV [] [] = []
zipWith fT fV (ex :: restx) (ey :: resty) =
    fV ex ey :: zipWith fT fV restx resty

-- -------------------------------------------------------------------- [ Show ]


show : (showFunc : {a : aTy} -> elemTy a -> String)
    -> (vs : DVect aTy elemTy l as)
    -> String
show showFunc vs {l} = unwords strL
  where
     asVStr : Vect l String
     asVStr = mapToVect showFunc vs

     strL : List String
     strL = ["["] ++ intersperse ","  (toList asVStr) ++ ["]"]

-- -------------------------------------------------------------------- [ Elem ]


data VElem : (iTy : Type)
          -> (elemTy : iTy -> Type)
          -> (e : elemTy i)
          -> (es : DVect iTy elemTy l is)
          -> (prf : Elem i is)
          -> Type
  where
    Hier : (x=y) -> VElem iTy eTy x (y::xs) Here
    Er   : (komst : VElem iTy eTy x xs later)
        -> VElem iTy eTy x (not_x::xs) (There later)

Uninhabited (VElem iTy eTy a Nil prf) where
  uninhabited (Hier _) impossible
  uninhabited (Er _) impossible

vectIsEmpty : DecEq iTy => VElem iTy eTy e [] prf -> Void
vectIsEmpty (Hier _) impossible
vectIsEmpty (Er _) impossible

elemsNotEqual : DecEqIdx iTy eTy => (contra : (ex = ey) -> Void) -> VElem iTy eTy ex (ey :: rest) Here -> Void
elemsNotEqual contra (Hier Refl) = contra Refl

notInVect : DecEqIdx iTy eTy
        => (contra : VElem iTy eTy ex rest later -> Void)
        -> VElem iTy eTy ex (ey :: rest) (There later) -> Void
notInVect contra (Er komst) = contra komst

isElem' : {eTy : iTy -> Type}
       -> (DecEqIdx iTy eTy)
       => (e  : eTy i)
       -> (es : DVect iTy eTy l is)
       -> (prf : Elem i is)
       -> Dec (VElem iTy eTy e es prf)
isElem' ex (ey :: rest) Here with (decEq ex ey Refl)
  isElem' ey (ey :: rest) Here | (Yes Refl) = Yes (Hier Refl)
  isElem' ex (ey :: rest) Here | (No contra) = No (elemsNotEqual contra)

isElem' ex (ey :: rest) (There later) with (isElem' ex rest later)
  isElem' ex (ey :: rest) (There later) | (Yes komst) = Yes (Er komst)
  isElem' ex (ey :: rest) (There later) | (No contra) =
    No (notInVect contra)

isElem : {eTy : iTy -> Type}
      -> (DecEqIdx iTy eTy)
      => (e  : eTy i)
      -> (es : DVect iTy eTy l is)
      -> {auto prf : Elem i is}
      -> Dec (VElem iTy eTy e es prf)
isElem e es {prf} = isElem' e es prf


dropElem : (as : DVect iTy eTy (S l) is)
        -> (prf : VElem iTy eTy a as idx)
        -> DVect iTy eTy l (dropElem is idx)
dropElem (a :: x) (Hier _) = x
dropElem {l = (S k)} (not_x :: xs) (Er komst) =
  not_x :: dropElem xs komst

-- --------------------------------------------------------------------- [ EOF ]
