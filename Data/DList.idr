-- --------------------------------------------------------------- [ DList.idr ]
-- Module    : DList.idr
-- Copyright : (c) 2015,2016,2017 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| A `list` construct to create lists of dependent types.
|||
||| One of the problems with using dependent types is that types
||| depend on values. This affects the ability to construct lists of
||| values that have a dependent type. The existing `List` type cannot
||| be used as it requires all elements to have the same type.
module Data.DList

import Data.List

import public Decidable.Equality.Indexed

%access export

using (aTy : Type, elemTy : (aTy -> Type), x : aTy)

  ||| A list construct for dependent types.
  |||
  ||| @aTy    The type of the value contained within the list element type.
  ||| @elemTy The type of the elements within the list
  ||| @as     The List used to contain the different values within the type.
  public export
  data DList : (aTy : Type)
            -> (elemTy : aTy -> Type)
            -> (as : List aTy)
            -> Type where
    ||| Create an empty List
    Nil  : DList aTy elemTy Nil
    ||| Cons
    |||
    ||| @elem The element to add
    ||| @rest The list for `elem` to be added to.
    (::) : (elem : elemTy x)
        -> (rest : DList aTy elemTy xs)
        -> DList aTy elemTy (x::xs)

%name DList rest

-- -------------------------------------------------------------- [ Form Tests ]
isNil : DList aTy eTy as -> Bool
isNil Nil     = True
isNil (x::xs) = False

isCons : DList aTy eTy as -> Bool
isCons l = isNil l == False

-- ------------------------------------------- [ Predicates that are Decidable ]

public export
data NonEmpty : (xs : DList aTy eTy as) -> Type where
  IsNonEmpty : DList.NonEmpty (x::rest)

Uninhabited (DList.NonEmpty []) where
  uninhabited IsNonEmpty impossible

nonEmpty : (xs : DList aTy eTy as) -> Dec (NonEmpty xs)
nonEmpty Nil            = No absurd
nonEmpty (elem :: rest) = Yes IsNonEmpty

public export
data InBounds : (idx : Nat)
             -> (xs  : DList aTy eTy as)
             -> Type
  where
    InFirst : DList.InBounds Z (x::rest)
    InLater : (later : DList.InBounds idx rest)
           -> DList.InBounds (S idx) (x :: rest)

Uninhabited (DList.InBounds idx []) where
  uninhabited InFirst impossible
  uninhabited (InLater _) impossible

inBounds : (idx : Nat)
        -> (xs  : DList aTy eTy as)
        -> Dec (InBounds idx xs)
inBounds idx Nil = No uninhabited
inBounds Z (elem :: rest) = Yes InFirst
inBounds (S k) (elem :: rest) with (inBounds k rest)
  inBounds (S k) (elem :: rest) | (Yes prf) = Yes $ InLater prf
  inBounds (S k) (elem :: rest) | (No contra) =
      No (\p => case p of
                   InLater y => contra y)

-- ------------------------------------------------------------------ [ Length ]

public export
length : DList aTy eTy as -> Nat
length Nil     = Z
length (x::xs) = (S Z) + length xs

Sized (DList aTy eTy as) where
  size = length

-- ---------------------------------------------------------------- [ Indexing ]

public export
index : (idx : Nat)
     -> (xs  : DList aTy eTy as)
     -> {auto ok : InBounds idx xs}
     -> {auto ok' : List.InBounds idx as}
     -> eTy (index idx as)
index Z (y :: rest) {ok = InFirst} = y
index (S k) (y :: rest) {ok = (InLater later)} {ok' = (InLater x)} = index k rest

public export
head : (xs : DList aTy eTy (a::as)) -> eTy a
head (y :: rest) = y

public export
tail : (xs : DList aTy eTy (a :: as))
    -> (DList aTy eTy as)
tail (x :: rest) = rest


public export
last : (xs : DList aTy eTy as)
    -> {auto ok : NonEmpty xs}
    -> {auto ok' : NonEmpty as}
    -> eTy (last as)
last [] {ok = IsNonEmpty} {ok' = _} impossible
last (elem :: []) {ok = ok} {ok' = ok'} = elem
last (elem :: (y :: rest)) {ok = ok} {ok' = ok'} = last (y::rest)

public export
init : (xs : DList aTy eTy as)
    -> {auto ok  : NonEmpty xs}
    -> {auto ok' : NonEmpty as}
    -> DList aTy eTy (init as)
init [] {ok = IsNonEmpty} {ok' = _} impossible
init (elem :: []) {ok = ok} {ok' = ok'} = []
init (elem :: (y :: rest)) {ok = ok} {ok' = ok'} = elem :: init (y::rest)

-- --------------------------------------------------------- [ Bob The Builder ]

public export
(++) : DList aTy eTy xs
    -> DList aTy eTy ys
    -> DList aTy eTy (xs ++ ys)
(++) Nil     ys = ys
(++) (x::xs) ys = x :: (xs ++ ys)

public export
replicate : (n : Nat)
         -> elemTy a
         -> DList aTy elemTy (replicate n a)
replicate Z x = Nil
replicate (S k) x = x :: replicate k x

-- ---------------------------------------------------------------- [ SubLists ]

public export
take : (n : Nat)
    -> DList aTy elemTy as
    -> DList aTy elemTy (take n as)
take Z rest = Nil
take (S k) [] = []
take (S k) (elem :: rest) = elem :: take k rest

takeWhile : ({a : aTy} -> elemTy a -> Bool)
         -> DList aTy elemTy as
         -> (bs : List aTy ** DList aTy elemTy bs)
takeWhile p Nil     = (_ ** Nil)
takeWhile p (x::xs) =
    if p x
      then (_ ** DList.(::) x (snd (takeWhile p xs)))
      else (_ ** Nil)

public export
drop : (n : Nat)
    -> DList aTy elemTy as
    -> DList aTy elemTy (drop n as)
drop Z     rest = rest
drop (S k) [] = []
drop (S k) (elem :: rest) = drop k rest

dropWhile : ({a : aTy} -> elemTy a -> Bool)
         -> DList aTy elemTy as
         -> (bs : List aTy ** DList aTy elemTy bs)
dropWhile p Nil     = (_ ** Nil)
dropWhile p (x::xs) =
    if p x
      then dropWhile p xs
      else (_ ** DList.(::) x xs)

-- ---------------------------------------------------------------- [ Equality ]

equals : ({a,b : aTy} -> elemTy a -> elemTy b -> Bool)
       -> DList aTy elemTy as
       -> DList aTy elemTy bs
       -> Bool
equals _ Nil     Nil     = True
equals p (x::xs) (y::ys) =
  if p x y
    then equals p xs ys
    else False
equals _ _       _       = False

-- ------------------------------------------------------------------- [ Order ]

compare : ({a,b : aTy} -> elemTy a -> elemTy b -> Bool)
        -> ({a,b : aTy} -> elemTy a -> elemTy b -> Ordering)
        -> DList aTy elemTy as
        -> DList aTy elemTy bs
        -> Ordering
compare _  _   Nil     Nil     = EQ
compare _  _   Nil     _       = LT
compare _  _   _       Nil     = GT
compare eq cmp (x::xs) (y::ys) =
  if not $ eq x y
    then cmp x y
    else compare eq cmp xs ys

-- ----------------------------------------------------------------- [ Folding ]
-- TODO

foldr : ({a : aTy} -> elemTy a -> p -> p)
     -> p
     -> DList aTy elemTy as
     -> p
foldr f init Nil     = init
foldr f init (x::xs) = f x (DList.foldr f init xs)

foldl : ({a : aTy} -> p -> elemTy a -> p)
      -> p
      -> DList aTy elemTy as
      -> p
foldl f init Nil = init
foldl f init (x::xs) = DList.foldl f (f init x) xs

-- ----------------------------------------------------------------- [ Functor ]

mapToList : ({a : aTy} -> elemTy a -> b)
         -> DList aTy elemTy as
         -> List b
mapToList f Nil     = List.Nil
mapToList f (x::xs) = f x :: mapToList f xs

-- TODO map from one DList to another.

mapMaybe : ({a : aTy} -> elemTy a -> Maybe b)
         -> DList aTy elemTy as
         -> List b
mapMaybe f Nil     = Nil
mapMaybe f (x::xs) =
  case f x of
    Nothing => mapMaybe f xs
    Just y  => y :: mapMaybe f xs

concatMap : Monoid m
         => (func : {a : aTy} -> elemTy a -> m)
         -> (xs : DList aTy elemTy as)
         -> m
concatMap f = foldr (\e, res => f e <+> res) neutral

namespace Clean
  traverse : Applicative f
          => {bTy : Type}
          -> {elemTyB : bTy -> Type}
          -> (funcTy : aTy -> bTy)
          -> (func : {a : aTy} -> elemTy a -> f $ elemTyB (funcTy a))
          -> (xs   : DList aTy elemTy as)
          -> f (DList bTy elemTyB (map funcTy as))
  traverse fTy func Nil     = pure Nil
  traverse fTy func (x::xs) = [| DList.(::) (func x) (traverse fTy func xs) |]

namespace ToList
 traverseToList : Applicative f
        => (func : {a : aTy} -> elemTy a -> f b)
        -> (xs   : DList aTy elemTy as)
        -> f (List b)
 traverseToList func Nil     = pure Nil
 traverseToList func (x::xs) = [| (::) (func x) (ToList.traverseToList func xs) |]

traverseToLDP : Applicative f
             => {bTy : Type}
             -> {elemTyB : bTy -> Type}
             -> (func : {a : aTy}
                     -> elemTy a
                     -> f (c ** elemTyB c))
             -> (xs : DList aTy elemTy as)
             -> f (List (b ** elemTyB b))
traverseToLDP func [] = pure Nil
traverseToLDP func (e :: rest) = [| List.(::) (func e) $ traverseToLDP func rest|]

-- --------------------------------------------------------- [ Transformations ]
-- TODO

||| From list of Dependent Pairs.
fromLDP : List (x : aTy ** eTy x)
       -> (as ** DList aTy eTy as)
fromLDP Nil     = (_ ** DList.Nil)
fromLDP (x::xs) = (_ ** DList.(++) [snd x] (snd $ fromLDP xs))

namespace Clean
  fromLDP : (xs : List (x : aTy ** eTy x))
         -> (DList aTy eTy (map DPair.fst xs))
  fromLDP [] = Nil
  fromLDP (x :: xs) = snd x :: Clean.fromLDP xs

-- ---------------------------------------------- [ To List of Dependent Pairs ]

||| To List of Dependent Pairs
toLDP : DList aTy eTy as
     -> List (x : aTy ** eTy x)
toLDP Nil     = Nil
toLDP (x::xs) = (_**x) :: toLDP xs

||| List to DList
fromList : {ty : Type}
        -> {e : ty -> Type}
        -> {x : ty}
        -> (es : List (e x))
        -> DList ty e (replicate (length es) x)
fromList [] = Nil
fromList (x :: xs) = x :: fromList xs

-- -------------------------------------------------------- [ Membership Tests ]

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

-- TODO elem

hasAnyBy : ({a,b : aTy} -> elemTy a -> elemTy b -> Bool)
         -> DList aTy elemTy as
         -> DList aTy elemTy bs
         -> Bool
hasAnyBy p es  Nil     = False
hasAnyBy p Nil es      = False
hasAnyBy p es  (x::xs) =
  if elemBy p x es
    then True
    else hasAnyBy p es xs

-- TODO hasAny

-- --------------------------------------------------------------- [ Searching ]

find : ({a : aTy} -> elemTy a -> Bool)
    -> DList aTy elemTy as
    -> Maybe $ DPair aTy elemTy
find p Nil     = Nothing
find p (x::xs) =
  if p x
    then Just (_ ** x)
    else find p xs

private
findIndex' : Nat
          -> ({a : aTy} -> elemTy a -> Bool)
          -> DList aTy elemTy as
          -> Maybe Nat
findIndex' cnt p Nil     = Nothing
findIndex' cnt p (x::xs) =
    if p x
      then Just cnt
      else findIndex' (S cnt) p xs

findIndex : ({a : aTy} -> elemTy a -> Bool)
         -> DList aTy elemTy as
         -> Maybe Nat
findIndex = findIndex' Z


private
findIndices' : Nat
            -> ({a : aTy} -> elemTy a -> Bool)
            -> DList aTy elemTy as
            -> List Nat
findIndices' cnt p Nil     = Nil
findIndices' cnt p (x::xs) =
    if p x
      then cnt :: findIndices' (S cnt) p xs
      else findIndices' (S cnt) p xs

findIndices : ({a : aTy} -> elemTy a -> Bool)
           -> DList aTy elemTy as
           -> List Nat
findIndices = findIndices' Z

elemIndexBy : ({a,b : aTy} -> elemTy a -> elemTy b -> Bool)
            -> elemTy a
            -> DList aTy elemTy as
            -> Maybe Nat
elemIndexBy p e = findIndex (\x => p e x)

-- TODO elemIndex

elemIndicesBy : ({a,b : aTy} -> elemTy a -> elemTy b -> Bool)
              -> elemTy a
              -> DList aTy elemTy as
              -> List Nat
elemIndicesBy p e = findIndices (\x => p e x)


-- TODO elemIndicies

-- ------------------------------------------------------------- [ Conversions ]
-- TODO

-- ----------------------------------------------------------------- [ Filters ]
-- TODO

-- ------------------------------------------------------------ [ Partitioning ]
-- TODO



span : ({a : aTy} -> elemTy a -> Bool)
    -> DList aTy elemTy xys
    -> ((xs ** DList aTy elemTy xs), (ys ** DList aTy elemTy ys))
span f Nil     = ((_ ** Nil), (_ ** Nil))
span f (x::xs) =
  if f x
    then let ((_ ** ys),(_ ** zs)) = span f xs
           in ((_ ** x::ys), (_ ** zs))
    else ((_ ** Nil), (_ ** (x::xs)))

break : ({a : aTy} -> elemTy a -> Bool)
      -> DList aTy elemTy xys
      -> ((xs ** DList aTy elemTy xs), (ys ** DList aTy elemTy ys))
break f xs = span (not . f) xs

split : ({a : aTy} -> elemTy a -> Bool)
     -> DList aTy elemTy xys
     -> (xxs ** DList (List aTy) (\xs => DList aTy elemTy xs) xxs)
split f xs =
  case break f xs of
    ((_ ** chunk), (_ ** Nil))     => (_ ** [chunk])
    ((_ ** chunk), (_ ** (y::ys))) => let (_ ** rest) = DList.split f ys
        in (_ ** DList.(::) chunk rest)


-- ----------------------------------------------------------------- [ Zipping ]
-- TODO

-- -------------------------------------------------------------- [ Predicates ]
-- TODO

-- ----------------------------------------------------------------- [ Sorting ]
-- TODO

mergeBy : Ord aTy => ({a,b : aTy} -> elemTy a -> elemTy b -> Ordering)
        -> DList aTy elemTy as
        -> DList aTy elemTy bs
        -> (cs ** DList aTy elemTy cs) -- Someday replace with (sort (as ++ bs))
mergeBy cmp Nil right = (_ ** right)
mergeBy cmp left Nil  = (_ ** left)
mergeBy cmp (x::xs) (y::ys) =
  if cmp x y == LT
    then let (_ ** rest) = mergeBy cmp xs      (y::ys) in (_ ** DList.(::) x rest)
    else let (_ ** rest) = mergeBy cmp (x::xs) ys      in (_ ** DList.(::) y rest)


-- -------------------------------------------------------------------- [ Show ]

||| Function to show a `DList`.
|||
||| Due to limitations in idris wrt to class instances on dependent
||| types a generic show instance cannot be defined for
||| sigmalist. This will cause minor annoyances in its use.
|||
||| @showFunc A function to show the elements
||| @l       The list to be Shown.
showDList : (showFunc : {a : aTy} -> elemTy a -> String)
         -> (l : DList aTy elemTy as)
         -> String
showDList f xs = "[" ++ unwords (intersperse "," (mapToList f xs)) ++ "]"


-- -------------------------------------------------------------- [ Predicates ]
||| Proof that some element is found in a `DList`.
|||
||| @iTy     The type of the element's index.
||| @elemTy  The type of the list element.
||| @x       An element in the list.
||| @xs      The list itself.
||| @prf     Proof that the element's index is in the list in the same position as the element itself.
public export
data DElem : (iTy    : Type)
          -> (elemTy : iTy -> Type)
          -> (x      : elemTy i)
          -> (xs     : DList iTy elemTy is)
          -> (prf    : Elem i is)
          -> Type
    where
      ||| Proof that the element is at the front of the list.
      Hier : (x=y) -> DElem ity elemTy x (y :: xs) Here

      ||| Proof that the element is found later in the list.
      Er : (komst : DElem iTy elemTy x xs xs') -> DElem iTy elemTy x (x' ::xs) (There xs')

Uninhabited (DElem iTy elemTy a Nil prf) where
    uninhabited (Hier _) impossible
    uninhabited (Er _) impossible

%name DElem komst


notInList : DecEqIdx iTy eTy
         => (contra : DElem iTy eTy ex rest later -> Void)
         -> DElem iTy eTy ex (ey :: rest) (There later)
         -> Void
notInList contra (Er komst) = contra komst

elemsNotEqual : DecEqIdx iTy eTy
             => (contra : (ex = ey) -> Void)
             -> DElem iTy eTy ex (ey :: rest) Here
             -> Void
elemsNotEqual contra (Hier Refl) = contra Refl

isElem' : {eTy : iTy -> Type}
       -> (DecEqIdx iTy eTy)
       => (e : eTy i)
       -> (es : DList iTy eTy is)
       -> (prf : Elem i is)
       -> Dec (DElem iTy eTy e es prf)
isElem' ex (ey :: rest) Here with (decEq ex ey Refl)
  isElem' ey (ey :: rest) Here | (Yes Refl) = Yes (Hier Refl)
  isElem' ex (ey :: rest) Here | (No contra) = No (elemsNotEqual contra)

isElem' ex (ey :: rest) (There later) with (isElem' ex rest later)
  isElem' ex (ey :: rest) (There later) | (Yes prf) = Yes (Er prf)
  isElem' ex (ey :: rest) (There later) | (No contra) =
    No (notInList contra)

isElem : {eTy : iTy -> Type}
      -> (DecEqIdx iTy eTy)
      => (e : eTy i)
      -> (es : DList iTy eTy is)
      -> {auto prf : Elem i is}
      -> Dec (DElem iTy eTy e es prf)
isElem e es {prf} = isElem' e es prf

||| Analgous to `delete` for normal Lists, however, we require explicit proof that the element, and its index, are in the list.
|||
||| @a   The element to remove.
||| @as  The list to remove the element from.
||| @idx Proof that the index of `a` is in the type of `as`.
||| @prf Proof that the element's index is in the list in the same positino as the element itself.
delete' : (a    : elemTy i)
       -> (as   : DList iTy elemTy is)
       -> (idx  : Elem i is)
       -> (prf  : DElem iTy elemTy a as idx)
       -> DList iTy elemTy (dropElem is idx)
delete' a (a  :: rest) Here          (Hier Refl) = rest
delete' a (a' :: rest) (There later) (Er komst)  = a' :: delete' a rest later komst

||| Analgous to `delete` for normal Lists, however, we must first calculate proof that the element, and its index, are in the list.
|||
||| @a   The element to remove.
||| @as  The list to remove the element from.
delete : (a        : elemTy i)
      -> (as       : DList iTy elemTy is)
      -> {auto idx : Elem i is}
      -> {auto prf : DElem iTy elemTy a as idx}
      -> DList iTy elemTy (dropElem is idx)
delete x xs {idx} {prf} = delete' x xs idx prf

||| Remove an element from the list given proof of its, and its
||| index's, location in the list.
|||
||| @as  The list to remove the element from.
||| @prf Proof that the element's index is in the list in the same
|||      position as the element itself.
public export
dropElem : (as  : DList iTy elemTy is)
        -> (prf : DElem iTy elemTy a as idx)
        -> DList iTy elemTy (dropElem is idx)
dropElem (a  :: rest) (Hier Refl)       = rest
dropElem (a' :: rest) (Er komst) = a' :: dropElem rest komst

namespace Alt
  index : (xs  : DList iTy eTy is)
       -> (idx : Elem i is)
       -> eTy i
  index (ex :: rest) Here = ex
  index (ex :: rest) (There later) = index rest later

  update : (vs  : DList iTy eTy is)
        -> (idx : Elem i is)
        -> (new : eTy i)
        -> DList iTy eTy is
  update (ex :: rest) Here new = new :: rest
  update (ex :: rest) (There later) new = ex :: update rest later new

-- --------------------------------------------------------------------- [ EOF ]
