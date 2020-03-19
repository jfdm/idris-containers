module Data.List.Predicates.Unique

import public Data.List.NotElem

%default total
%access public export

data Unique : (prfSame : a -> a -> Type)
            -> (ns : List a)
            -> Type
  where
    Empty : Unique p Nil
    Extend : (node : a)
          -> (prfNotElem : NotElem p node ns)
          -> (rest : Unique p ns)
          -> Unique p (node :: ns)

nodeIsFoundLater : (contra : NotElem prfSame x xs -> Void)
                -> Unique prfSame (x :: xs)
                -> Void
nodeIsFoundLater contra (Extend x prfNotElem rest) = contra prfNotElem

restNotUnique : (contra : Unique prfSame xs -> Void)
             -> (prfX : NotElem prfSame x xs)
             -> Unique prfSame (x :: xs)
             -> Void
restNotUnique contra prfX (Extend x prfNotElem rest) = contra rest

unique : (decEq : (x,y : a) -> Dec (prfSame x y))
     -> (xs    : List a)
     -> Dec (Unique prfSame xs)
unique decEq [] = Yes Empty
unique decEq (x :: xs) with (notElem decEq x xs)
  unique decEq (x :: xs) | (Yes prfX) with (unique decEq xs)
    unique decEq (x :: xs) | (Yes prfX) | (Yes prfXS) = Yes (Extend x prfX prfXS)
    unique decEq (x :: xs) | (Yes prfX) | (No contra) = No (restNotUnique contra prfX)

  unique decEq (x :: xs) | (No contra) = No (nodeIsFoundLater contra)

toList : {ns : List a} -> Unique prfSame ns -> List a
toList Empty = []
toList (Extend node prfNotElem rest) = node :: toList rest

-- --------------------------------------------------------------------- [ EOF ]
