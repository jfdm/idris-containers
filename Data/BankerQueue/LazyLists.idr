||| This is not actually a general lazy list library. It's really
||| intended for implementing banker's queues. It also has some
||| junk about regular lists for that purpose.
module Data.BankerQueue.LazyLists

%default total
%access public

||| A lazy-spined list.
data LList : Type -> Type where
  Nil : LList a
  (::) : (x : a) -> (xs : Lazy (LList a)) -> LList a
%name LList xs, ys, zs

instance Eq a => Eq (LList a) where
  (==) [] [] = True
  (==) [] (x :: xs) = False
  (==) (x :: xs) [] = False
  (==) (x :: xs) (y :: ys) = x == y && Force xs == Force ys

tailsSame : {x : a} -> {xs : List a} -> {y : a} -> {ys : List a} -> x :: xs = y :: ys -> xs = ys
tailsSame Refl = Refl

headsSame : {x : a} -> {xs : List a} -> {y : a} -> {ys : List a} -> x :: xs = y :: ys -> x = y
headsSame Refl = Refl

tailsSameL : {x : a} -> {xs : LList a} -> {y : a} -> {ys : LList a} -> x :: xs = y :: ys -> xs = ys
tailsSameL Refl = Refl

headsSameL : {x : a} -> {xs : LList a} -> {y : a} -> {ys : LList a} -> x :: xs = y :: ys -> x = y
headsSameL Refl = Refl

forceSameSame : (x,y : Lazy a) -> Force x = Force y -> x = y
forceSameSame (Delay x) (Delay x) Refl = Refl

delayForce : Delay {t=LazyEval} (Force {t=LazyEval} x) = x
delayForce = Refl

-- We would prefer not to force `xs` and `ys` in the `No` case, when their
-- values are not needed. Unfortunately, the elaborator's laziness
-- machinery seems to make that impossible, or at least too difficult.
-- If I write `No ?whatever`, the type I get for `whatever` is no good for
-- the job, and nothing similar seems to work either. Fortunately, it
-- shouldn't really be a big deal.
instance DecEq a => DecEq (LList a) where
  decEq [] [] = Yes Refl
  decEq [] (x :: xs) = No (\Refl impossible)
  decEq (x :: xs) [] = No (\Refl impossible)
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: Delay xs) (x :: Delay ys) | (Yes Refl) with (decEq xs ys)
      decEq (x :: Delay xs) (x :: Delay xs) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (x :: Delay xs) (x :: Delay ys) | (Yes Refl) | (No contra) = No (\ab => contra (tailsSameL ab))
    decEq (x :: Delay xs) (y :: Delay ys) | (No contra) = No (\ab => contra (headsSameL ab))

instance Functor LList where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

||| Append two lazy lists.
(++) : LList a -> LList a -> LList a
(++) [] ys = ys
(++) (x :: xs) ys = x :: Delay (Force xs ++ ys)

length : LList a -> Nat
length [] = Z
length (x :: xs) = S (length xs)

lengthAppend : (left : LList a) -> (right : LList a) ->
               length (left ++ right) = length left + length right
lengthAppend [] right = Refl
lengthAppend (x :: xs) right = rewrite lengthAppend xs right in Refl

mapPreservesLength : (f : a -> b) ->
                     (l : LList a) ->
                     length (map f l) = length l
mapPreservesLength f [] = Refl
mapPreservesLength f (x :: xs) = cong $ mapPreservesLength f xs

appendAssociative : (l,c,r : LList a) ->
                    l ++ c ++ r = (l ++ c) ++ r
appendAssociative [] c r = Refl
appendAssociative (x :: xs) c r =
  rewrite appendAssociative xs c r in Refl

lListToList : LList a -> List a
lListToList [] = []
lListToList (x :: xs) = x :: lListToList xs

listToLList : List a -> LList a
listToLList [] = []
listToLList (x :: xs) = x :: listToLList xs

lListToListDistributesOverAppend : (l, r : LList a) ->
                                   lListToList (l ++ r) = lListToList l ++ lListToList r
lListToListDistributesOverAppend [] r = Refl
lListToListDistributesOverAppend (x :: xs) r =
  rewrite lListToListDistributesOverAppend xs r in Refl

appendNilRightNeutralL : (xs : LList a) -> xs ++ [] = xs
appendNilRightNeutralL [] = Refl
appendNilRightNeutralL (x :: Delay xs) = cong {f = (x ::)} (appendNilRightNeutralL xs)

reverseOnto : List a -> List a -> List a
reverseOnto [] ys = ys
reverseOnto (x :: xs) ys = reverseOnto xs (x :: ys)

myReverse : List a -> List a
myReverse xs = reverseOnto xs []

-- Reverses a `List` onto the front of an `LList`
reverseOntoL : List a -> LList a -> LList a
reverseOntoL [] ys = ys
reverseOntoL (x :: xs) ys = reverseOntoL xs (x :: ys)

-- Reverse a `List`, turning it into an `LList`
reverseL : List a -> LList a
reverseL xs = reverseOntoL xs []

rotateOnto : List a -> LList a -> LList a
rotateOnto xs ys = ys ++ reverseL xs

reverseOntoLSumsLength : (xs : List a) -> (ys : LList a) -> length (xs `reverseOntoL` ys) = length xs + length ys
reverseOntoLSumsLength [] ys = Refl
reverseOntoLSumsLength (x :: xs) ys =
  rewrite reverseOntoLSumsLength xs (x :: ys)
  in sym $ plusSuccRightSucc _ _

reverseOntoSumsLength : (xs : List a) -> (ys : List a) -> length (xs `reverseOnto` ys) = length xs + length ys
reverseOntoSumsLength [] ys = Refl
reverseOntoSumsLength (x :: xs) ys =
  rewrite reverseOntoSumsLength xs (x :: ys)
  in sym $ plusSuccRightSucc _ _

reverseLPreservesLength : (l : List a) -> length (reverseL l) = length l
reverseLPreservesLength xs =
  rewrite sym $ plusZeroRightNeutral (length xs)
  in reverseOntoLSumsLength xs []

lListToListPreservesLength : (l : LList a) -> length (lListToList l) = length l
lListToListPreservesLength [] = Refl
lListToListPreservesLength (x :: xs) = cong (lListToListPreservesLength xs)

rotateOntoSumsLength : (xs : List a) -> (ys : LList a) -> length (xs `rotateOnto` ys) = length ys + length xs
rotateOntoSumsLength xs ys = rewrite sym $ reverseLPreservesLength xs in lengthAppend ys _

reverseOntoReversesOnto : (xs, ys : List a) -> xs `reverseOnto` ys = myReverse xs ++ ys
reverseOntoReversesOnto [] ys = Refl
reverseOntoReversesOnto (x :: xs) ys =
  rewrite reverseOntoReversesOnto xs (x :: ys)
  in rewrite appendAssociative (reverseOnto xs []) [x] ys
  in cong {f = (++ys)} (sym $ reverseOntoReversesOnto xs [x])

reverseOntoLReversesOnto : (xs : List a) -> (ys : LList a) -> lListToList (xs `reverseOntoL` ys) = myReverse xs ++ lListToList ys
reverseOntoLReversesOnto [] ys = Refl
reverseOntoLReversesOnto (x :: xs) ys =
  rewrite reverseOntoLReversesOnto xs (x :: ys)
  in rewrite appendAssociative (reverseOnto xs []) [x] (lListToList ys)
  in cong {f = (++lListToList ys)} (sym $ reverseOntoReversesOnto xs [x])
