||| A `list` construct to create lists of dependent types.
|||
||| One of the problems with using dependent types is that types
||| depend on values. This affects the ability to construct lists of
||| values that have a dependent type. The existing `List` type cannot
||| be used as it requires all elements to have the same type.
module Data.Sigma.DList

%access public
--%default total

using (aTy : Type, elemTy : (aTy -> Type), x : aTy)

  ||| A list construct for dependent types.
  |||
  ||| @aTy    The type of the value contained within the list element type.
  ||| @elemTy The type of the elements within the list
  ||| @as     The List used to contain the different values within the type.
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

{- TODO Safely Index the List

index : (n : Nat)
     -> (l : DList aTy eTy as)
     -> (ok : lt n (length l) = True)
     -> (a : aTy ** eTy a)
index Z     (x::xs) p    = (_ ** x)
index (S n) (x::xs) p    = index n xs ...
index _     Nil     Refl   impossible
-}

index : (n : Nat)
     -> (l : DList aTy eTy as)
     -> Maybe $ Sigma aTy eTy
index Z     (x::xs) = Just (_ ** x)
index (S n) (x::xs) = index n xs
index _     Nil     = Nothing

head : (l : DList aTy eTy as) -> {auto ok : isCons l = True} -> Sigma aTy eTy
head Nil     {ok=Refl}   impossible
head (x::xs) {ok=p}    = (_ ** x)

tail : (l : DList aTy eTy (a :: as))
    -> {auto ok : isCons l = True}
    -> (DList aTy eTy as)
tail Nil     {ok=Refl}   impossible
tail (x::xs) {ok=p}    = xs


last : (l : DList aTy eTy as) -> {auto ok : isCons l = True} -> Sigma aTy eTy
last Nil           {ok=Refl}  impossible
last [x]           {ok=p}     = (_ ** x)
last xs@(x::y::ys) {ok=p}     = last (assert_smaller xs (y::ys)) {ok=Refl}

-- TODO init

-- ---------------------------------------------- [ To List of Dependent Pairs ]

toLDP : DList aTy eTy as -> List (x : aTy ** eTy x)
toLDP Nil     = Nil
toLDP (x::xs) = (_**x) :: toLDP xs

fromList : {ty : Type} -> {e : ty -> Type} -> {x : ty}
         -> List (e x) -> (es : List ty ** DList ty e es)
fromList Nil     = (_ ** DList.Nil)
fromList (x::xs) = (_ ** DList.(::) x (getProof (fromList xs)))

-- --------------------------------------------------------- [ Bob The Builder ]

(++) : DList aTy eTy xs -> DList aTy eTy ys -> DList aTy eTy (xs ++ ys)
(++) Nil     ys = ys
(++) (x::xs) ys = x :: (xs ++ ys)


-- infixl 4 ++=

-- (++=) : List (eTy x) -> (ys ** List ty ** DList aTy eTy (xs ++ ys))
-- (++=) xs ys =

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

-- ----------------------------------------------------------- [ List to DList ]


-- -------------------------------------------------------------------- [ Show ]
-- A way of doing show, a little nasty but worth it.

private
doDListShow : ({a : aTy} -> elemTy a -> String)
           -> DList aTy elemTy as
           -> List String
doDListShow _    Nil    = Nil
doDListShow f es with (es)
            | Nil      = Nil
            | (b::bs)  = (f b) :: doDListShow f bs

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

-- ---------------------------------------------------------------------- [ Eq ]

eqDList : (eqFunc : {a,b : aTy} -> elemTy a -> elemTy b -> Bool)
           -> (x : DList aTy elemTy xs)
           -> (y : DList aTy elemTy ys)
           -> Bool
eqDList _  Nil    Nil    = True
eqDList _  Nil    ys     = False
eqDList _  xs     Nil    = False
eqDList f (x::xs) (y::ys) = if f x y then eqDList f xs ys else False


-- ------------------------------------------- [ Applicative/Monad/Traversable ]
-- TODO

-- -------------------------------------------------------- [ Decidable Equals ]
-- TODO

-- --------------------------------------------------------------------- [ EOF ]
