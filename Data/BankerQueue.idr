module Data.BankerQueue
import Data.BankerQueue.LazyLists

%default total
%access public

||| Okasaki-style Banker's queue
record Queue a where
  constructor MkQueue
  frontDiff : Nat -- How much longer the front of the queue is than the rear
  front : Lazy $ LList a
  rearLen : Nat
  rear : List a
  rearValid : length rear = rearLen
  diffValid : length front = frontDiff + length rear
  -- diffValid is last because its proofs are longest
  
||| Convert a queue to a list
queueToList : Queue a -> List a
queueToList q = lListToList (front q) ++ myReverse (rear q)

||| Convert a list to a queue
listToQueue : List a -> Queue a
listToQueue xs = let frnt = listToLList xs in MkQueue (length frnt) frnt Z [] Refl (sym $ plusZeroRightNeutral (length frnt))

||| Convert a queue to a lazy list
queueToLList : Queue a -> LList a
queueToLList q = rear q `rotateOnto` front q

infix 5 ===
||| Equivalence of queues, using propositional equality of the elements.
(===) : Queue a -> Queue a -> Type
(===) q1 q2 = queueToList q1 = queueToList q2

length : Queue a -> Nat
length q = frontDiff q + rearLen q + rearLen q

lengthCorrect : (q : Queue a) -> length q = length (queueToList q)
lengthCorrect (MkQueue frontDiff front rearLen rear rearValid diffValid) =
  rewrite sym rearValid
  in rewrite sym diffValid
  in rewrite lengthAppend (lListToList (Force front)) (reverseOnto rear [])
  in rewrite reverseOntoSumsLength rear []
  in rewrite plusZeroRightNeutral (length rear)
  in rewrite lListToListPreservesLength front
  in Refl

equivSameLength : (q1, q2 : Queue a) -> q1 === q2 -> length q1 = length q2
equivSameLength q1 q2 eq =
  rewrite lengthCorrect q1
  in rewrite lengthCorrect q2
  in rewrite eq
  in Refl

-- Some experimentation may be required to find the best way to do this.
instance Eq a => Eq (Queue a) where
  (==) q1 q2 = length q1 == length q2 && queueToLList q1 == queueToLList q2

{-
TODO Finish this
decEquiv : DecEq a => (q1, q2 : Queue a) -> Dec (q1 === q2)
decEquiv q1 q2 with (decEq (length q1) (length q2))
  decEquiv q1 q2 | (No contra) = No (\ab => contra (equivSameLength q1 q2 ab))
  decEquiv q1 q2 | (Yes prf) with (decEq (queueToLList q1) (queueToLList q2))

    decEquiv q1 q2 | (Yes prf) | (Yes sl) = Yes $

       ?decEquiv_rhs_1
    decEquiv q1 q2 | (Yes prf) | (No contra) = No (\ab => ?decEquiv_rhs_2)
    -}

empty : Queue a
empty = MkQueue Z [] Z [] Refl Refl

snoc : Queue a -> a -> Queue a
snoc (MkQueue (S k) front rearLen rear rearValid diffValid) x =
  MkQueue k front (S rearLen) (x :: rear) (rewrite rearValid in Refl)
    (rewrite diffValid in plusSuccRightSucc k (length rear))
snoc (MkQueue Z front rearLen rear rearValid diffValid) x =
  MkQueue (S (2 * length rear)) (rotateOnto (x :: rear) front) Z [] Refl $
      rewrite rotateOntoSumsLength (x :: rear) front
      in rewrite sym diffValid
      in rewrite plusZeroRightNeutral (length front)
      in rewrite plusZeroRightNeutral (length front + length front)
      in sym $ plusSuccRightSucc _ _

||| `snoc` actually does what it's supposed to do, relative to
||| `queueToList`. That is, snoccing an element onto a queue
||| appends the corresponding singleton to its list representation.
snocSnocs : (q : Queue a) -> (x : a) -> queueToList (q `snoc` x) = queueToList q ++ [x]
snocSnocs (MkQueue (S k) front rearLen rear rearValid diffValid) x =
  rewrite reverseOntoReversesOnto rear [x]
  in appendAssociative (lListToList front) (reverseOnto rear []) [x]
snocSnocs (MkQueue Z (Delay front) rearLen rear rearValid diffValid) x =
  rewrite lListToListDistributesOverAppend front (reverseOntoL rear (x :: Delay []))
  in rewrite reverseOntoLReversesOnto rear (x :: Delay [])
  in rewrite sym $ appendAssociative (lListToList front) (reverseOnto rear []) [x]
  in appendNilRightNeutral _

||| A view of the front of a queue.
data FrontView : Queue a -> Type where
  FVEmpty : FrontView empty
  FVCons : (hd : a) -> (tl : Queue a) -> queueToList q = hd :: queueToList tl -> FrontView q

-- There are some weird things in here that I seemed to need to do to satisfy
-- the termination checker. I don't know why.
||| View the front of a queue.
frontView : (q : Queue a) -> FrontView q
frontView (MkQueue Z [] Z [] Refl Refl) = FVEmpty
frontView (MkQueue _ _ Z (y :: ys) rearValid diffValid) = (\Refl impossible) rearValid
frontView (MkQueue _ _ (S k) [] rearValid diffValid) = (\Refl impossible) rearValid
frontView (MkQueue frontDiff [] rearLen (x :: xs) rearValid diffValid) = absurd $ trans diffValid $ plusCommutative frontDiff (length (x :: xs))
frontView (MkQueue Z (x :: xs) Z [] rearValid diffValid) = (\Refl impossible) diffValid
frontView (MkQueue Z (x :: xs) (S k) [] rearValid diffValid) = (\Refl impossible) rearValid
frontView (MkQueue Z (x :: xs) Z (y :: ys) Refl diffValid) impossible
frontView (MkQueue Z (x :: xs) (S k) (y :: ys) rearValid diffValid) =
  FVCons x (MkQueue (k + S k) ((y :: ys) `rotateOnto` xs) Z [] Refl $
             (rewrite lengthAppend xs (reverseOntoL ys [y])
              in rewrite succInjective _ _ diffValid
              in rewrite reverseOntoLSumsLength ys [y]
              in rewrite succInjective _ _ rearValid
              in rewrite plusZeroRightNeutral (k + S k)
              in rewrite plusCommutative k 1 in Refl)) $
             rewrite appendNilRightNeutral (lListToList (xs ++ reverseOntoL ys [y]))
             in rewrite lListToListDistributesOverAppend (Force xs) (reverseOntoL ys (y :: Delay []))
             in rewrite reverseOntoReversesOnto ys [y]
             in rewrite reverseOntoLReversesOnto ys [y]
             in Refl
frontView (MkQueue (S k) [] rearLen rear rearValid diffValid) = (\Refl impossible) diffValid
frontView (MkQueue (S k) (x :: xs) rearLen rear rearValid diffValid) =
  FVCons x (MkQueue k xs rearLen rear rearValid (succInjective _ _ diffValid)) Refl

||| Attempts to remove an element from the front of the queue.
||| Returns `Nothing` if the queue is empty.
uncons : Queue a -> Maybe (a, Queue a)
uncons q with (frontView q)
  uncons (MkQueue Z (Delay []) Z [] Refl Refl) | FVEmpty = Nothing
  uncons q | (FVCons hd tl prf) = Just (hd, tl)

instance Functor Queue where
  map f (MkQueue frontDiff front rearLen rear rearValid diffValid) =
        MkQueue frontDiff (map f front) rearLen (map f rear) (rewrite mapPreservesLength f rear in rearValid)
        (rewrite mapPreservesLength f rear in rewrite mapPreservesLength f front in diffValid)

