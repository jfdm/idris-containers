-- --------------------------------------------------------------- [ DList.idr ]
-- Module    : DList.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
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

-- ------------------------------------------------------------------ [ Length ]

length : DList aTy eTy as -> Nat
length Nil     = Z
length (x::xs) = (S Z) + length xs

-- ---------------------------------------------------------------- [ Indexing ]

-- TODO Safely Index the List

index : (n : Nat)
     -> (l : DList aTy eTy as)
     -> Maybe $ DPair aTy eTy
index Z     (x::xs) = Just (_ ** x)
index (S n) (x::xs) = index n xs
index _     Nil     = Nothing

head : (l : DList aTy eTy as)
    -> {auto ok : isCons l = True}
    -> DPair aTy eTy
head Nil     {ok=Refl}   impossible
head (x::xs) {ok=p}    = (_ ** x)

tail : (l : DList aTy eTy (a :: as))
    -> {auto ok : isCons l = True}
    -> (DList aTy eTy as)
tail Nil     {ok=Refl}   impossible
tail (x::xs) {ok=p}    = xs


last : (l : DList aTy eTy as)
    -> {auto ok : isCons l = True}
    -> DPair aTy eTy
last Nil           {ok=Refl}  impossible
last [x]           {ok=p}     = (_ ** x)
last xs@(x::y::ys) {ok=p}     = last (assert_smaller xs (y::ys)) {ok=Refl}

-- TODO Safely init the list
-- TODO Unsafely init the list.

-- --------------------------------------------------------- [ Bob The Builder ]

(++) : DList aTy eTy xs
    -> DList aTy eTy ys
    -> DList aTy eTy (xs ++ ys)
(++) Nil     ys = ys
(++) (x::xs) ys = x :: (xs ++ ys)

-- TODO replicate

replicate : {a : aTy}
         -> Nat
         -> elemTy a
         -> (as : List aTy ** DList aTy elemTy as)
replicate Z     x = (_ ** Nil)
replicate (S Z) x = (_ ** DList.(::) x Nil)
replicate (S n) x = (_ ** DList.(::) x (snd (replicate n x)))

-- ---------------------------------------------------------------- [ SubLists ]

take : Nat
    -> DList aTy elemTy as
    -> (bs : List aTy ** DList aTy elemTy bs)
take Z     xs      = (_ ** Nil)
take (S n) Nil     = (_ ** Nil)
take (S n) (x::xs) = (_ ** DList.(::) x (snd (take n xs)))

takeWhile : ({a : aTy} -> elemTy a -> Bool)
         -> DList aTy elemTy as
         -> (bs : List aTy ** DList aTy elemTy bs)
takeWhile p Nil     = (_ ** Nil)
takeWhile p (x::xs) =
    if p x
      then (_ ** DList.(::) x (snd (takeWhile p xs)))
      else (_ ** Nil)

drop : Nat
    -> DList aTy elemTy as
    -> (bs : List aTy ** DList aTy elemTy bs)
drop Z     xs      = (_ ** Nil)
drop (S n) Nil     = (_ ** Nil)
drop (S n) (x::xs) = (_ ** snd (drop n xs))

dropWhile : ({a : aTy} -> elemTy a -> Bool)
         -> DList aTy elemTy as
         -> (bs : List aTy ** DList aTy elemTy bs)
dropWhile p Nil     = (_ ** Nil)
dropWhile p (x::xs) =
    if p x
      then dropWhile p xs
      else (_ ** DList.(::) x xs)

-- ---------------------------------------------------------------- [ Equality ]

eqDList : ({a,b : aTy} -> elemTy a -> elemTy b -> Bool)
       -> DList aTy elemTy as
       -> DList aTy elemTy bs
       -> Bool
eqDList _ Nil     Nil     = True
eqDList p (x::xs) (y::ys) =
  if p x y
    then eqDList p xs ys
    else False
eqDList _ _       _       = False

-- ------------------------------------------------------------------- [ Order ]

cmpDList : ({a,b : aTy} -> elemTy a -> elemTy b -> Bool)
        -> ({a,b : aTy} -> elemTy a -> elemTy b -> Ordering)
        -> DList aTy elemTy as
        -> DList aTy elemTy bs
        -> Ordering
cmpDList _  _   Nil     Nil     = EQ
cmpDList _  _   Nil     _       = LT
cmpDList _  _   _       Nil     = GT
cmpDList eq cmp (x::xs) (y::ys) =
  if not $ eq x y
    then cmp x y
    else cmpDList eq cmp xs ys

-- ----------------------------------------------------------------- [ Folding ]
-- TODO

foldr : ({a : aTy} -> elemTy a -> p -> p)
     -> p
     -> DList aTy elemTy as -> p
foldr f init Nil     = init
foldr f init (x::xs) = f x (DList.foldr f init xs)

foldl : ({a : aTy} -> p -> elemTy a -> p)
      -> p
      -> DList aTy elemTy as -> p
foldl f init Nil = init
foldl f init (x::xs) = DList.foldl f (f init x) xs

-- ----------------------------------------------------------------- [ Functor ]

mapDList : ({a : aTy} -> elemTy a -> b)
       -> DList aTy elemTy as
       -> List b
mapDList f Nil     = List.Nil
mapDList f (x::xs) = with List f x :: mapDList f xs

-- TODO map from one DList to another.

mapMaybe : ({a : aTy} -> elemTy a -> Maybe b)
         -> DList aTy elemTy as
         -> List b
mapMaybe f Nil     = Nil
mapMaybe f (x::xs) =
  case f x of
    Nothing => mapMaybe f xs
    Just y  => y :: mapMaybe f xs

-- TODO mapMaybe from one DList to another

-- --------------------------------------------------------- [ Transformations ]
-- TODO

||| From list of Dependent Pairs.
fromLDP : List (x : aTy ** eTy x)
       -> (as ** DList aTy eTy as)
fromLDP Nil     = (_ ** DList.Nil)
fromLDP (x::xs) = (_ ** DList.(++) [snd x] (snd $ fromLDP xs))

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
        -> List (e x)
        -> (es : List ty ** DList ty e es)
fromList Nil     = (_ ** DList.Nil)
fromList (x::xs) = (_ ** DList.(::) x (snd (fromList xs)))

toLDP' : {ty : Type} -> {x : ty} -> {e : ty -> Type}
      -> List (e x) -> List (x : ty ** e x)
toLDP' Nil     = Nil
toLDP' (x::xs) = (_ ** x) :: toLDP' xs

fromList' : {ty : Type}
       -> {e : ty -> Type}
       -> {x : ty}
       -> List (e x)
       -> (es : List ty ** DList ty e es)
fromList' xs = fromLDP $ toLDP' xs

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
-- A way of doing show, a little nasty but worth it.
private
doDListShow : ({a : aTy} -> elemTy a -> String)
           -> DList aTy elemTy as
           -> List String
doDListShow _  Nil     = Nil
doDListShow f  (x::xs) = (f x) :: doDListShow f xs

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
showDList f xs = "[" ++ unwords (intersperse "," (doDListShow f xs)) ++ "]"


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
      Hier : DElem ity elemTy x (x :: xs) Here

      ||| Proof that the element is found later in the list.
      Er : (komst : DElem iTy elemTy x xs xs') -> DElem iTy elemTy x (x' ::xs) (There xs')

Uninhabited (DElem iTy elemTy a Nil prf) where
    uninhabited Hier impossible
    uninhabited (Er _) impossible

%name DElem komst

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
delete' a (a  :: rest) Here          Hier       = rest
delete' a (a' :: rest) (There later) (Er komst) = a' :: delete' a rest later komst

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
dropElem (a  :: rest) Hier       = rest
dropElem (a' :: rest) (Er komst) = a' :: dropElem rest komst

-- --------------------------------------------------------------------- [ EOF ]
