module Data.List.Fixes

%default total
%access export

public export
data PrefixOfBy : (holdsFor : type -> type -> Type)
               -> (pref  : List type)
               -> (input : List type)
               -> Type where
   Empty  : PrefixOfBy p Nil xs
   Extend : (prf : p x y)
         -> PrefixOfBy p xs ys
         -> PrefixOfBy p (x::xs) (y::ys)

rightIsEmpty : PrefixOfBy p (x :: xs) [] -> Void
rightIsEmpty Empty impossible
rightIsEmpty (Extend _ _) impossible

notPrefix : (contra : p x y -> Void)
         -> PrefixOfBy p (x :: xs) (y :: ys)
         -> Void
notPrefix contra (Extend prf x) = contra prf

restNotPrefix : (contra : PrefixOfBy p xs ys -> Void)
             -> PrefixOfBy p (x :: xs) (y :: ys)
             -> Void
restNotPrefix contra (Extend x y) = contra y


isPrefixOfBy : (test : (x,y : type) -> Dec (p x y))
            -> (pref, input : List type)
            -> (Dec $ PrefixOfBy p pref input)
isPrefixOfBy test [] input = Yes Empty
isPrefixOfBy test (x :: xs) [] = No rightIsEmpty
isPrefixOfBy test (x :: xs) (y :: ys) with (test x y)
  isPrefixOfBy test (x :: xs) (y :: ys) | (Yes prf) with (isPrefixOfBy test xs ys)
    isPrefixOfBy test (x :: xs) (y :: ys) | (Yes prf) | (Yes z) = Yes (Extend prf z)
    isPrefixOfBy test (x :: xs) (y :: ys) | (Yes prf) | (No contra) =
      No (restNotPrefix contra)

  isPrefixOfBy test (x :: xs) (y :: ys) | (No contra) =
      No (notPrefix contra)


isPrefixOf : DecEq type
          => (pref, input : List type)
          -> Dec $ PrefixOfBy (=) pref input
isPrefixOf = isPrefixOfBy decEq

public export
SuffixOfBy : (holdsFor : type -> type -> Type)
          -> (pref  : List type)
          -> (input : List type)
          -> Type
SuffixOfBy holdsFor pref input =
  PrefixOfBy holdsFor (reverse pref) (reverse input)

isSuffixOfBy : (test : (x,y : type) -> Dec (p x y))
            -> (pref, input : List type)
            -> (Dec $ SuffixOfBy p pref input)
isSuffixOfBy test pref input =
  isPrefixOfBy test (reverse pref) (reverse input)



isSuffixOf : DecEq type
          => (suf, input : List type)
          -> (Dec $ SuffixOfBy (=) suf input)
isSuffixOf suf input =
  isSuffixOfBy decEq suf input
