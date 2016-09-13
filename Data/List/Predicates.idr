-- ---------------------------------------------------------- [ Predicates.idr ]
-- Module    : Predicates.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| More Quantifiers for Lists, but keeping them out of the prelude so
||| need a new module name.
module Data.List.Predicates


%default total
%access public export

||| `proof` that an element is not in a list.
data NotElem : a -> List a -> Type where
  NotHere  : NotElem x []
  NotThere : Eq ty
          => {x,y : ty}
          -> (prf : x /= y = True)
          -> NotElem x xs
          -> NotElem x (y::xs)

||| AllDiff, the list is made of unique elements.
data AllDiff : List a -> Type where
  EmptyCase : AllDiff Nil
  OneCase   : AllDiff [x]
  ManyCase  : NotElem x xs -> AllDiff xs -> AllDiff (x::xs)


-- --------------------------------------------------------------------- [ EOF ]
