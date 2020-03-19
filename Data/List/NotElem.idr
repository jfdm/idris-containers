module Data.List.NotElem

%default total
%access public export

data NotElem : (prfEq : a -> a -> Type) -> a -> List a -> Type where
  IsEmpty : NotElem prfEq x Nil
  NotFirst : (prf : Not (prfEq x y)) -> NotElem prfEq x Nil -> NotElem prfEq x [y]
  NotThere : (prf : Not (prfEq x y))
          -> (notLater : NotElem prfEq x there)
          -> NotElem prfEq x (y::there)

isFirstElem : (decEq : (x : a) -> (y : a) -> Dec (prfSame x y))
           -> (prf : prfSame n x)
           -> NotElem prfSame n (x :: xs)
           -> Void
isFirstElem decEq prf (NotFirst f x) = f prf
isFirstElem decEq prf (NotThere f notLater) = f prf

isFoundLater : (decEq : (x : a) -> (y : a) -> Dec (prfSame x y))
            -> (contra : prfSame n x -> Void)
            -> (f : NotElem prfSame n xs -> Void)
            -> NotElem prfSame n (x :: xs)
            -> Void
isFoundLater decEq contra f (NotFirst prf x) = f x
isFoundLater decEq contra f (NotThere prf notLater) = f notLater

notElem : (decEq : (x,y : a) -> Dec (prfSame x y))
       -> (n : a)
       -> (ns : List a)
       -> Dec (NotElem prfSame n ns)
notElem decEq n [] = Yes IsEmpty
notElem decEq n (x :: xs) with (decEq n x)
  notElem decEq n (x :: xs) | (Yes prf) = No (isFirstElem decEq prf)
  notElem decEq n (x :: xs) | (No contra) with (notElem decEq n xs)
    notElem decEq n (x :: xs) | (No contra) | (Yes prf) = Yes (NotThere contra prf)
    notElem decEq n (x :: xs) | (No contra) | (No f) = No (isFoundLater decEq contra f)

-- --------------------------------------------------------------------- [ EOF ]
