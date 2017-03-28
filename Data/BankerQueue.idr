module Data.BankerQueue
import Data.BankerQueue.LazyLists
import Data.BankerQueue.WellFounded

%default total
%access public

||| Okasaki-style Banker's queue. This is actually an output-restricted
||| deque.
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
record (===) (q1 : Queue a) (q2 : Queue a) where
  constructor MkEquiv
  getEquiv : queueToList q1 = queueToList q2

{-
(===) : Queue a -> Queue a -> Type
(===) q1 q2 = queueToList q1 = queueToList q2
-}

||| Converting a queue to a list and back gives you an equivalent queue.
queueToFromList : (q : Queue a) -> listToQueue (queueToList q) === q
queueToFromList q = MkEquiv $
  rewrite listToFromLList (lListToList (Force (front q)) ++ reverseOnto (rear q) [])
  in rewrite appendNilRightNeutral
                         (lListToList (Force (front q)) ++
                         reverseOnto (rear q) [])
  in Refl

||| Converting a list to a queue and back gives you the same list.
listToFromQueue : (xs : List a) -> queueToList (listToQueue xs) = xs
listToFromQueue xs = rewrite listToFromLList xs in appendNilRightNeutral xs

||| The number of elements in a queue
length : Queue a -> Nat
length q = frontDiff q + rearLen q + rearLen q

||| `length q` gives the same result as converting `q` to a list and
||| calculating its length.
lengthCorrect : (q : Queue a) -> length q = length (queueToList q)
lengthCorrect (MkQueue frontDiff front rearLen rear rearValid diffValid) =
  rewrite sym rearValid
  in rewrite sym diffValid
  in rewrite lengthAppend (lListToList (Force front)) (reverseOnto rear [])
  in rewrite reverseOntoSumsLength rear []
  in rewrite plusZeroRightNeutral (length rear)
  in rewrite lListToListPreservesLength front
  in Refl

||| Equivalent queues have equal lengths.
lengthPreservesEquiv : (q1, q2 : Queue a) -> q1 === q2 -> length q1 = length q2
lengthPreservesEquiv q1 q2 eq =
  rewrite lengthCorrect q1
  in rewrite lengthCorrect q2
  in rewrite getEquiv eq
  in Refl

-- Some experimentation may be required to find the best way to do this.
instance Eq a => Eq (Queue a) where
  (==) q1 q2 = length q1 == length q2 && queueToLList q1 == queueToLList q2

toListViaLList : (q : Queue a) -> lListToList (queueToLList q) = queueToList q
toListViaLList q = rewrite lListToListDistributesOverAppend (Force (front q)) (reverseOntoL (rear q) [])
                   in rewrite lListToListReverseOntoL (rear q) []
                   in Refl

toLListEqEquiv : (q1, q2 : Queue a) -> queueToLList q1 = queueToLList q2 -> q1 === q2
toLListEqEquiv q1 q2 prf = MkEquiv $
  rewrite sym $ toListViaLList q1
  in rewrite sym $ toListViaLList q2
  in cong {f = lListToList} prf

toLListViaList : (q : Queue a) -> listToLList (queueToList q) = queueToLList q
toLListViaList q =
  rewrite listToLListDistributesOverAppend
             (lListToList (Force (front q)))
             (reverseOnto (rear q) [])
  in rewrite sym $ lListToListReverseOntoL (rear q) []
  in rewrite lListToFromList (Force (front q))
  in rewrite lListToFromList (reverseOntoL (rear q) [])
  in Refl

toListEqToLList : (q1, q2 : Queue a) -> q1 === q2 -> queueToLList q1 = queueToLList q2
toListEqToLList q1 q2 prf =
  rewrite sym $ toLListViaList q1
  in rewrite sym $ toLListViaList q2
  in cong {f = listToLList} (getEquiv prf)

||| If `a` has decidable equality, then `Queue a` has decidable equivalence.
decEquiv : DecEq a => (q1, q2 : Queue a) -> Dec (q1 === q2)
decEquiv q1 q2 with (decEq (length q1) (length q2))
  decEquiv q1 q2 | (No contra) = No (\ab => contra (lengthPreservesEquiv q1 q2 ab))
  decEquiv q1 q2 | (Yes prf) with (decEq (queueToLList q1) (queueToLList q2))
    decEquiv q1 q2 | (Yes prf) | (Yes sl) = Yes (toLListEqEquiv q1 q2 sl)
    decEquiv q1 q2 | (Yes prf) | (No contra) = No (contra . toListEqToLList q1 q2)

||| The empty queue
Empty : Queue a
Empty = MkQueue Z [] Z [] Refl Refl

||| Converting the empty queue to a list yields the empty list.
emptyIsEmpty : queueToList Empty = []
emptyIsEmpty = Refl

||| Add an element to the end of a queue
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

||| `snoc` adds one to the length of a queue.
snocLength : (q : Queue a) -> (x : a) -> length (snoc q x) = length q + 1
snocLength q x =
  rewrite lengthCorrect q
  in rewrite lengthCorrect (snoc q x)
  in rewrite snocSnocs q x
  in rewrite List.lengthAppend (lListToList (Force (front q)) ++
                   reverseOnto (rear q) []) [x]  
  in Refl

||| Snoccing the same element onto two equivalent queues yields equivalent
||| queues.
snocPreservesEquiv : (q1, q2 : Queue a) -> (x : a) -> q1 === q2 -> (q1 `snoc` x) === (q2 `snoc` x)
snocPreservesEquiv q1 q2 x q1q2 = MkEquiv $
  rewrite snocSnocs q1 x
  in rewrite snocSnocs q2 x
  in rewrite getEquiv q1q2
  in Refl

||| Adds an element to the *front* of a queue.
cons : a -> Queue a -> Queue a
cons x (MkQueue frontDiff front rearLen rear rearValid diffValid) =
  MkQueue (S frontDiff) (x :: front) rearLen rear rearValid (cong diffValid)

||| `cons` behaves properly relative to `queueToList`.
consConses : (x : a) -> (q : Queue a) -> queueToList (x `cons` q) = x :: queueToList q
consConses x (MkQueue frontDiff front rearLen rear rearValid diffValid) = Refl

||| `cons` behaves properly relative to `length`.
consLength : (x : a) -> (q : Queue a) -> length (cons x q) = S (length q)
consLength x (MkQueue frontDiff front rearLen rear rearValid diffValid) = Refl

||| Consing the same element onto two equivalent queues yields equivalent
||| queues.
consPreservesEquiv : (x : a) -> (q1, q2 : Queue a) -> q1 === q2 -> (x `cons` q1) === (x `cons` q2)
consPreservesEquiv x q1 q2 q1q2 = MkEquiv $
  rewrite consConses x q1
  in rewrite consConses x q2
  in rewrite getEquiv q1q2
  in Refl

rearsEqRearLensEq : (xs, ys : Queue a) -> rear xs = rear ys -> rearLen xs = rearLen ys
rearsEqRearLensEq (MkQueue frontDiff front rearLen rear rearValid diffValid) (MkQueue k x j rear y z) Refl =
  rewrite sym rearValid
  in rewrite y in Refl

reflsSame : (x, y : a) -> (p,q : x = y) -> p = q
reflsSame x x Refl Refl = Refl

mkQueue : (fd : Nat ) -> (frnt : LList a) -> (rr : List a) -> (dv : length frnt = fd + length rr) -> Queue a
mkQueue fd frnt rr dv = MkQueue fd (Delay frnt) (length rr) rr Refl dv

queueSamemkQueue : (q : Queue a) -> q = mkQueue (frontDiff q) (front q) (rear q) (diffValid q)
queueSamemkQueue (MkQueue frontDiff (Delay front) (List.length rear) rear Refl diffValid) = Refl

-- This horrifying thing works around type dependencies.
private
sameListsEqual_lem : (fd1 : Nat) -> (fr1 : LList a) -> (rl1 : Nat) -> (rr1 : List a) -> (rv1 : length rr1 = rl1) -> (dv1 : length fr1 = fd1 + length rr1) -> 
 (fd2 : Nat) -> (fr2 : LList a) -> (rl2 : Nat) -> (rr2 : List a) -> (rv2 : length rr2 = rl2) -> (dv2 : length fr2 = fd2 + length rr2) -> 
 fr1 = fr2 -> rr1 = rr2 ->
 MkQueue fd1 fr1 rl1 rr1 rv1 dv1 = MkQueue fd2 fr2 rl2 rr2 rv2 dv2
sameListsEqual_lem fd1 fr1 (List.length rr1) rr1 Refl dv1 fd2 fr1 (List.length rr1) rr1 Refl dv2 Refl Refl with (plusRightCancel fd1 fd2 (length rr1) $ sym dv1 `trans` dv2)
  sameListsEqual_lem fd1 fr1 (List.length rr1) rr1 Refl dv1 fd1 fr1 (List.length rr1) rr1 Refl dv2 Refl Refl | Refl =
    rewrite reflsSame (length fr1) (fd1 + length rr1) dv1 dv2 in Refl

||| If two queues have the same front and rear lists, then they are in fact equal.
sameListsEqual : (xs, ys : Queue a) -> Force (front xs) = Force (front ys) -> rear xs = rear ys -> xs = ys
sameListsEqual (MkQueue fd1 (Delay fr1) rl1 rr1 rv1 dv1) (MkQueue fd2 (Delay fr2) rl2 rr2 rv2 dv2) fronts rears =
    (sameListsEqual_lem fd1 fr1 rl1 rr1 rv1 dv1 fd2 fr2 rl2 rr2 rv2 dv2 fronts rears)

||| A view of the front of a queue.
data FrontView : Queue a -> Type where
  FVEmpty : FrontView Empty
  FVCons : (hd : a) -> (tl : Queue a) -> queueToList q = hd :: queueToList tl -> FrontView q

-- There are some weird things in here that I seemed to need to do to satisfy
-- the totality checker. I don't know why.
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

-- TODO head and tail should use default strategies
-- that recognize that  q `snoc` x  is never empty, if at all
-- possible. That is, if we can find evidence that `q` is the
-- result of `snoc`, we should grab it.
||| Get the head of a queue.
head : (q : Queue a) -> {auto m : Nat} -> {auto nonempty : length q = S m} -> a
head {nonempty} q with (frontView q)
  head {nonempty} (MkQueue Z (Delay []) Z [] Refl Refl) | FVEmpty = absurd nonempty
  head {nonempty} q | (FVCons hd tl prf) = hd

||| Get the tail of a queue.
tail : (q : Queue a) -> {auto m : Nat} -> {auto nonempty : length q = S m} -> Queue a
tail {nonempty} q with (frontView q)
  tail {nonempty} (MkQueue Z (Delay []) Z [] Refl Refl) | FVEmpty = absurd nonempty
  tail {nonempty} q | (FVCons hd tl prf) = tl

headCons : (x : a) -> (q : Queue a) -> head {m=length q} {nonempty=consLength x q} (cons x q) = x
headCons x q with (frontView (cons x q))
  headCons x (MkQueue Z [] Z [] Refl Refl) | FVEmpty impossible
  headCons x (MkQueue frontDiff front rearLen rear rearValid diffValid) | (FVCons hd tl prf) =
    sym $ headsSame prf

tailCons : (x : a) -> (q : Queue a) -> tail {m=length q} {nonempty=consLength x q} (cons x q) === q
tailCons x q with (frontView (cons x q))
  tailCons x (MkQueue Z [] Z [] Refl Refl) | FVEmpty impossible
  tailCons x (MkQueue frontDiff front rearLen rear rearValid diffValid) | (FVCons hd tl prf) =
    MkEquiv $ sym $ tailsSame prf

||| A view of the front of a queue based on `cons`. Unlike `FrontView`,
||| which should have an analogue for *any* queue representation, this
||| particular view is specific to output-restricted deques.
data FrontViewCons : Queue a -> Type where
  FVCEmpty : FrontViewCons Empty
  FVCCons : (hd : a) -> (tl : Queue a) -> (hd `cons` tl) === q -> FrontViewCons q

frontViewCons : (q : Queue a) -> FrontViewCons q
frontViewCons q with (frontView q)
  frontViewCons (MkQueue Z (Delay []) Z [] Refl Refl) | FVEmpty = FVCEmpty
  frontViewCons q | (FVCons hd tl prf) =
    FVCCons hd tl $ (MkEquiv $ rewrite consConses hd tl in sym prf)

||| Pull an element off the front (if there is one) and push it
||| on the back.
rotateLeftOnce : (q : Queue a) -> Queue a
rotateLeftOnce q with (frontView q)
  rotateLeftOnce _ | FVEmpty = Empty
  rotateLeftOnce q | FVCons hd tl _ = tl `snoc` hd

-- This could be written more efficiently by digging into the representation.
-- This way, however, is much easier.
splitAt : Nat -> Queue a -> (Queue a, Queue a)
splitAt Z q = (Empty, q)
splitAt (S n) q with (frontView q)
  splitAt (S n) _ | FVEmpty = (Empty, Empty)
  splitAt (S n) q | (FVCons hd tl prf) with (splitAt n tl)
    splitAt (S n) q | (FVCons hd tl prf) | (lefts, rights) = (cons hd lefts, rights)

instance Functor Queue where
  map f (MkQueue frontDiff front rearLen rear rearValid diffValid) =
        MkQueue frontDiff (map f front) rearLen (map f rear) (rewrite mapPreservesLength f rear in rearValid)
        (rewrite mapPreservesLength f rear in rewrite mapPreservesLength f front in diffValid)

-- Some thinking and testing may be required to figure out the best
-- Foldable instance.
instance Foldable Queue where
  foldr c n q = foldr c n (queueToList q)
  foldl f b q = foldl f b (queueToList q)
-- Consider foldr c n q = foldr c (foldl (flip c) n (rear q)) (Force (front q))
-- Consider foldl f b q = foldr (flip f) (foldl f b (Force $ front q)) (rear q)

||| ``q `ConsesTo` r`` means that it's possible to cons an element onto `q`
||| to get a queue equivalent to `r`. This is primarily useful because it is
||| a well-founded relation.
data ConsesTo : Queue a -> Queue a -> Type where
  ConsingOn : (x : a) -> (x `cons` q) === r -> ConsesTo q r

consesToWF' : {a : Type} -> WellFounded' (ConsesTo {a})
consesToWF' {a} =
  let foo = inverseImageWF' {a=Queue a} NatSucc (BankerQueue.length) natSuccWF'
  in coarserWF' (ConsesTo {a}) (NatSucc `On` BankerQueue.length) crs foo
    where
      crs : (xs, ys : Queue a) -> ConsesTo xs ys -> (NatSucc `On` length) xs ys
      crs xs ys (ConsingOn x prf) =
        rewrite sym $ lengthPreservesEquiv (cons x xs) ys prf
        in rewrite sym $ consLength x xs
        in Refl

-- TODO This ends up being *much* too hard to use, because the types
-- blow up to gargantuan size. This both slows type checking to a crawl
-- and, more importantly, makes the metavariables really hard to use.
-- Probably the right fix is to implement this using an Accessible *datatype*
-- as is currently found in contrib. I thought I could get away without
-- that, but I was wrong. Fortunately, the well-foundedness proofs below
-- can actually be transformed into the right sort of datatype in a
-- straightforward manner, so the effort isn't wasted.

||| An eliminator (induction principle) for `cons`. If you can prove
||| `P ys` for each `ys` such that ``x `cons` ys === xs``, then you
||| get a proof of `P xs`.
consElim : {a : Type} -> {P : Queue a -> Type} ->
           (step : (xs : Queue a) -> ((ys : Queue a) -> ys `ConsesTo` xs -> P ys) -> P xs) ->
           (zs : Queue a) -> P zs
consElim {P} step zs = consesToWF' zs P step

||| ``q `SnocsTo` r`` means that it's possible to cons
||| an element onto `q` to get a queue equivalent to `r`.
data SnocsTo : Queue a -> Queue a -> Type where
  SnoccingOn : (x : a) -> (q `snoc` x) === r -> SnocsTo q r

snocsToWF' : {a : Type} -> WellFounded' (SnocsTo {a})
snocsToWF' {a} =
  let foo = inverseImageWF' {a=Queue a} NatSucc (BankerQueue.length) natSuccWF'
  in coarserWF' (SnocsTo {a}) (NatSucc `On` BankerQueue.length) crs foo
    where
      crs : (xs, ys : Queue a) -> SnocsTo xs ys -> (NatSucc `On` length) xs ys
      crs xs ys (SnoccingOn x prf) =
        rewrite sym $ lengthPreservesEquiv (snoc xs x) ys prf
        in rewrite plusCommutative 1 (length xs)
        in rewrite sym $ snocLength xs x
        in Refl

||| An eliminator (induction principle) for `snoc`. If you can prove
||| `P ys` for each `ys` such that ``ys `snoc` x === xs``, then you
||| get a proof of `P xs`.
snocElim : {a : Type} -> {P : Queue a -> Type} ->
           (step : (xs : Queue a) -> ((ys : Queue a) -> ys `SnocsTo` xs -> P ys) -> P xs) ->
           (zs : Queue a) -> P zs
snocElim {P} step zs = snocsToWF' zs P step

infixl 7 <++

||| Remove all the elements from the front of the second argument
||| and snoc them onto the end of the first argument. This is
||| efficient if the second argument is short and the first is
||| long. The implementation demonstrates the utility of `consElim`.
(<++) : Queue a -> Queue a -> Queue a
(<++) {a} = consElim {P = const (Queue a -> Queue a)} step
  where
    step : (q2 : Queue a) ->
           ((q : Queue a) -> q `ConsesTo` q2 -> Queue a -> Queue a) ->
           (q1 : Queue a) -> Queue a
    step q2 ind q1 with (frontViewCons q2)
      step _  ind q1  | FVCEmpty = q1
      step q2 ind q1 | (FVCCons hd tl prf) = ind tl (ConsingOn hd (MkEquiv $ getEquiv prf)) (q1 `snoc` hd)

-- TODO Prove <++ correct

instance Semigroup (Queue a) where
  -- TODO This should be written using a more direct
  -- pattern-matching approach for efficiency and ease of proof.
  (<+>) = (<++)

instance Monoid (Queue a) where
  neutral = Empty

||| A synonym for `cons` that gives us access to list syntax
(::) : a -> Queue a -> Queue a
(::) = cons

||| A synonym for `Empty` that gives us access to list syntax
Nil : Queue a
Nil = Empty

instance Show a => Show (Queue a) where
  show q = show (queueToList q)
