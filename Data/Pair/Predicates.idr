module Data.Pair.Predicates

%default total
%access public export

data PairEq : (prfSame : a -> a -> Type)
               -> (l : (a,a))
               -> (r : (a,a))
               -> Type
  where
    AreSame : (ad : prfSame a d)
           -> (bc : prfSame b c)
           -> PairEq prfSame (a,b) (c,d)

fsNotSame : (decEq : (x : a) -> (y : a) -> Dec (prfSame x y))
         -> (contra : prfSame a1 d -> Void)
         -> PairEq prfSame (a1, b) (c, d)
         -> Void
fsNotSame decEq contra (AreSame ad bc) = contra ad

sfNotSame : (decEq : (x : a) -> (y : a) -> Dec (prfSame x y))
         -> (contra : prfSame b c -> Void)
         -> PairEq prfSame (a1, b) (c, d)
         -> Void
sfNotSame decEq contra (AreSame ad bc) = contra bc

pairEq : {a : Type}
      -> {prfSame : a -> a -> Type}
      -> (decEq : (x,y : a) -> Dec (prfSame x y))
      -> (l,r : Pair a a)
      -> Dec (PairEq prfSame l r)
pairEq decEq (a, b) (c, d) with (decEq a d)
  pairEq decEq (a, b) (c, d) | (Yes prfAD) with (decEq b c)
    pairEq decEq (a, b) (c, d) | (Yes prfAD) | (Yes prfBC) = Yes (AreSame prfAD prfBC)
    pairEq decEq (a, b) (c, d) | (Yes prfAD) | (No contra) = No (sfNotSame decEq contra)

  pairEq decEq (a, b) (c, d) | (No contra) = No (fsNotSame decEq contra)
