module Data.List.Predicates.Pairs

import public Data.List
import public Data.Pair.Predicates

import public Data.List.Predicates.Unique

%default total
%access public export


data UniquePairs : (prfSame : a -> a -> Type)
                -> (ps : List (Pair a a))
                -> Type
  where
    MkUniquePairs : (ps  : List (Pair a a))
            -> (prf : Unique (PairEq prfSame) ps)
            -> UniquePairs prfSame ps

pairsNotUnique : (decEq : (x : a) -> (y : a) -> Dec (prfSame x y))
              -> (contra : Unique (PairEq prfSame) ps -> Void)
              -> UniquePairs prfSame ps
              -> Void
pairsNotUnique decEq contra (MkUniquePairs ps prf) = contra prf

uniquePairs : (decEq : (x,y : a) -> Dec (prfSame x y))
           -> (ps : List (Pair a a))
           -> Dec (UniquePairs prfSame ps)
uniquePairs decEq ps with (unique (pairEq decEq) ps)
  uniquePairs decEq ps | (Yes prf) = Yes (MkUniquePairs ps prf)
  uniquePairs decEq ps | (No contra) = No (pairsNotUnique decEq contra)

data PairOrigin : (p : Pair a a)
               -> (src : List a)
               -> Type
  where
    MkPO : Elem a src
        -> Elem b src
        -> PairOrigin (MkPair a b) src

aNotInSrc : (contra : Elem a src -> Void) -> PairOrigin (a, b) src -> Void
aNotInSrc contra (MkPO x y) = contra x

bNotInSrc : (contra : Elem b src -> Void) -> PairOrigin (a, b) src -> Void
bNotInSrc contra (MkPO x y) = contra y

originPair : DecEq a
          => (p : Pair a a)
          -> (src : List a)
          -> Dec (PairOrigin p src)
originPair (a, b) src with (isElem a src)
  originPair (a, b) src | (Yes prfA) with (isElem b src)
    originPair (a, b) src | (Yes prfA) | (Yes prfB) = Yes (MkPO prfA prfB)
    originPair (a, b) src | (Yes prfA) | (No contra) = No (bNotInSrc contra)

  originPair (a, b) src | (No contra) = No (aNotInSrc contra)


data PairsOrigin : (orig  : List a)
                -> (pairs : List (Pair a a))
                -> Type
  where
   First : PairOrigin p orig -> PairsOrigin orig [p]
   Rest : PairOrigin p orig
       -> PairsOrigin orig ps
       -> PairsOrigin orig (p::ps)

listEmpty : PairsOrigin src [] -> Void
listEmpty (First _) impossible
listEmpty (Rest _ _) impossible


headNotRightRestEmpty : (contra : PairOrigin x src -> Void)
                     -> PairsOrigin src [x]
                     -> Void
headNotRightRestEmpty contra (First x) = contra x
headNotRightRestEmpty contra (Rest x y) = contra x

headRightRestNot : (contra : PairsOrigin src (y :: ys) -> Void)
                -> PairsOrigin src (x :: (y :: ys)) -> Void
headRightRestNot contra (Rest x y) = contra y

headNotRight : (contra : PairOrigin x src -> Void)
            -> PairsOrigin src (x :: (y :: ys))
            -> Void
headNotRight contra (Rest x y) = contra x

originPairs : DecEq a
           => (src : List a)
           -> (ps : List (Pair a a))
           -> Dec (PairsOrigin src ps)
originPairs src [] = No listEmpty
originPairs src (x :: xs) with (xs)
  originPairs src (x :: xs) | [] with (originPair x src)
    originPairs src ((a, b) :: xs) | [] | (Yes (MkPO y z)) = Yes (First (MkPO y z))
    originPairs src (x :: xs) | [] | (No contra) = No (headNotRightRestEmpty contra)

  originPairs src (x :: xs) | (y :: ys) with (originPair x src)
    originPairs src (x :: xs) | (y :: ys) | (Yes prfX) with (assert_total $ originPairs src (y::ys))
      originPairs src (x :: xs) | (y :: ys) | (Yes prfX) | (Yes prf) = Yes (Rest prfX prf)
      originPairs src (x :: xs) | (y :: ys) | (Yes prfX) | (No contra) = No (headRightRestNot contra)

    originPairs src (x :: xs) | (y :: ys) | (No contra) = No (headNotRight contra)
