module Data.Vect.Extra

import Data.Vect

%access export
%default total

namespace Equality
   vecEq : Eq type => Vect n type -> Vect m type -> Bool
   vecEq [] [] = True
   vecEq [] (x :: xs) = False
   vecEq (x :: xs) [] = False
   vecEq (x :: xs) (y :: ys) = x == y && vecEq xs ys

namespace Decidable
  namespace SameLength
    decEq : DecEq type
          => (n = m)
          -> (xs : Vect n type)
          -> (ys : Vect m type)
          -> Dec (xs = ys)
    decEq Refl xs ys with (decEq xs ys)
      decEq Refl ys ys | (Yes Refl) = Yes Refl
      decEq Refl xs ys | (No contra) = No contra

  namespace DiffLength

    vectorsDiffLength : DecEq type
                      => (contra : (n = m) -> Void)
                      -> {xs : Vect n type}
                      -> {ys : Vect m type}
                      -> (xs = ys) -> Void
    vectorsDiffLength contra Refl = contra Refl

    decEq : DecEq type
         => (xs : Vect n type)
         -> (ys : Vect m type)
         -> Dec (xs = ys)
    decEq xs ys {n} {m} with (decEq n m)
      decEq xs ys {n = m} {m = m} | (Yes Refl) = decEq Refl xs ys
      decEq xs ys {n = n} {m = m} | (No contra) = No (vectorsDiffLength contra)
